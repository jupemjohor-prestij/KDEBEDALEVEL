/**
 * KDE Cadastral CAD & Mapping Engine
 * Copyright © CPDG Johor
 */

var points = []; 
var legs = [];   
var lotRecords = []; 
var datumPoints = []; 

const LINK_TO_METER = 0.201168;

var undoStack = [];
var redoStack = [];

var selectedLegIndex = null; 
var selectedLegIndices = []; 
var selectedLotIndex = null; 

var pendingLegData = null; 
var snappedPoint = null; 

var canvas = document.getElementById('cadCanvas');
var parent = document.getElementById('canvasParent');
var ctx = canvas.getContext('2d');

var zoomFactor = 1;
var panX = 0;
var panY = 0;

var isPanning = false;
var isBoxSelecting = false;
var boxStart = null;
var boxCurrent = null;
var panStart = { x: 0, y: 0 };
var hasDraggedBox = false;

var pickTargetField = null; 
var isMeasureMode = false;
var measurePoints = [];

var isAreaMode = false;
var areaPoints = [];

var isLotCreationMode = false;
var activeLotPa = '';
var activeLotUpi = '';
var activeLotNodes = [];

var toastTimer = null;
var inspectedStationId = null;

/* Basemap Engine States */
var currentBasemap = 'google_sat';
var basemapAlpha = 0.85;
var tileCache = {};

window.onload = function() {
  resizeCanvas();
  setupCanvasListeners();
  setupKeyboardListeners();
  setupResizableSidebar();
  setupDragAndDrop();
  
  // Set default CRS to Johor Cassini (GDM2000)
  var crsDropdown = document.getElementById('crsSelect');
  if (crsDropdown) crsDropdown.value = 'johor_gdm2000';

  // Ensure canvas starts clean without any pre-added points
  points = [];
  datumPoints = [];
  legs = [];
  lotRecords = [];

  // Keep input fields blank
  document.getElementById('initialStn').value = '';
  document.getElementById('datumE').value = '';
  document.getElementById('datumN').value = '';
  document.getElementById('fromStn').value = '';
  document.getElementById('toStn').value = '';

  updateStnTable();
  updateLineLogDropdowns();
  updateTable();
  updateLotTable();
  updateUndoRedoUI();
  
  // Center camera over Wisma Persekutuan JB without adding station entities
  centerOnWismaPersekutuan();
};

window.onresize = function() {
  resizeCanvas();
  drawCAD();
};

/* --- Area Calculation Utility (Shoelace Formula) --- */
function computePolygonAreaAndPerimeter(coords) {
  if (!coords || coords.length < 3) {
    return { areaSqM: 0, areaHa: 0, areaAc: 0, areaSqFt: 0, perimeterM: 0 };
  }

  var n = coords.length;
  var pts = coords.slice();
  if (pts[0].e === pts[n - 1].e && pts[0].n === pts[n - 1].n) {
    pts.pop();
    n = pts.length;
  }
  if (n < 3) {
    return { areaSqM: 0, areaHa: 0, areaAc: 0, areaSqFt: 0, perimeterM: 0 };
  }

  var areaSum = 0;
  var perimeter = 0;
  for (var i = 0; i < n; i++) {
    var j = (i + 1) % n;
    areaSum += (pts[i].e * pts[j].n) - (pts[j].e * pts[i].n);
    perimeter += Math.hypot(pts[j].e - pts[i].e, pts[j].n - pts[i].n);
  }

  var areaSqM = Math.abs(areaSum) / 2.0;
  return {
    areaSqM: areaSqM,
    areaHa: areaSqM / 10000.0,
    areaAc: areaSqM / 4046.8564224,
    areaSqFt: areaSqM * 10.7639104,
    perimeterM: perimeter
  };
}

/* --- Basemap Tile Engine --- */
function setBasemap(type) {
  currentBasemap = type;
  drawCAD();
}

function changeBasemapOpacity(val) {
  basemapAlpha = parseInt(val, 10) / 100.0;
  drawCAD();
}

function getTileUrl(type, x, y, z) {
  switch(type) {
    case 'google_sat':
      return `https://mt1.google.com/vt/lyrs=y&x=${x}&y=${y}&z=${z}`;
    case 'google_streets':
      return `https://mt1.google.com/vt/lyrs=m&x=${x}&y=${y}&z=${z}`;
    case 'esri_sat':
      return `https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/${z}/${y}/${x}.jpg`;
    case 'esri_topo':
      return `https://server.arcgisonline.com/ArcGIS/rest/services/World_Topo_Map/MapServer/tile/${z}/${y}/${x}.jpg`;
    case 'osm':
      var subdomains = ['a', 'b', 'c'];
      var s = subdomains[(x + y) % subdomains.length];
      return `https://${s}.tile.openstreetmap.org/${z}/${x}/${y}.png`;
    default:
      return null;
  }
}

function wgs84ToTileXY(lat, lng, zoom) {
  var latRad = lat * Math.PI / 180;
  var n = Math.pow(2, zoom);
  var x = (lng + 180.0) / 360.0 * n;
  var y = (1.0 - Math.log(Math.tan(latRad) + (1.0 / Math.cos(latRad))) / Math.PI) / 2.0 * n;
  return { x: x, y: y };
}

function tileXYToWGS84(x, y, zoom) {
  var n = Math.pow(2, zoom);
  var lng = x / n * 360.0 - 180.0;
  var latRad = Math.atan(Math.sinh(Math.PI * (1 - 2 * y / n)));
  var lat = latRad * 180.0 / Math.PI;
  return { lat: lat, lng: lng };
}

function screenToCadCoords(scrX, scrY, padding, baseScale, minE, minN) {
  var unscaledX = (scrX - panX) / zoomFactor;
  var unscaledY = (scrY - panY) / zoomFactor;

  var e = minE + (unscaledX - padding) / baseScale;
  var n = minN + ((canvas.height - unscaledY) - padding) / baseScale;
  return { e: e, n: n };
}

/* --- Distortion-Free Affine Basemap Tile Renderer --- */
function renderBasemapTiles(minE, minN, baseScale, padding) {
  if (currentBasemap === 'none') return;

  var cTL = screenToCadCoords(0, 0, padding, baseScale, minE, minN);
  var cTR = screenToCadCoords(canvas.width, 0, padding, baseScale, minE, minN);
  var cBL = screenToCadCoords(0, canvas.height, padding, baseScale, minE, minN);
  var cBR = screenToCadCoords(canvas.width, canvas.height, padding, baseScale, minE, minN);

  var gpsCorners = [
    getWGS84Coords(cTL.e, cTL.n),
    getWGS84Coords(cTR.e, cTR.n),
    getWGS84Coords(cBL.e, cBL.n),
    getWGS84Coords(cBR.e, cBR.n)
  ];

  var minLat = Math.min(...gpsCorners.map(g => g.lat));
  var maxLat = Math.max(...gpsCorners.map(g => g.lat));
  var minLng = Math.min(...gpsCorners.map(g => g.lng));
  var maxLng = Math.max(...gpsCorners.map(g => g.lng));

  if (isNaN(minLat) || isNaN(maxLat) || minLat < -85 || maxLat > 85) return;

  var metersPerPixel = 1 / (baseScale * zoomFactor);
  var z = Math.round(Math.log2(156543.03392 / metersPerPixel));
  z = Math.max(1, Math.min(20, z));

  var tileTL = wgs84ToTileXY(maxLat, minLng, z);
  var tileBR = wgs84ToTileXY(minLat, maxLng, z);

  var startX = Math.floor(Math.min(tileTL.x, tileBR.x));
  var endX = Math.floor(Math.max(tileTL.x, tileBR.x));
  var startY = Math.floor(Math.min(tileTL.y, tileBR.y));
  var endY = Math.floor(Math.max(tileTL.y, tileBR.y));

  if ((endX - startX + 1) * (endY - startY + 1) > 64) return;

  ctx.save();
  ctx.globalAlpha = basemapAlpha;

  for (var tx = startX; tx <= endX; tx++) {
    for (var ty = startY; ty <= endY; ty++) {
      var key = `${currentBasemap}_${z}_${tx}_${ty}`;
      var img = tileCache[key];

      if (!img) {
        img = new Image();
        img.src = getTileUrl(currentBasemap, tx, ty, z);
        img.onload = function() { drawCAD(); };
        tileCache[key] = img;
      }

      if (img.complete && img.naturalWidth !== 0) {
        var nw = tileXYToWGS84(tx, ty, z);
        var ne = tileXYToWGS84(tx + 1, ty, z);
        var sw = tileXYToWGS84(tx, ty + 1, z);

        var cadNW = wgs84ToCassini(nw.lat, nw.lng);
        var cadNE = wgs84ToCassini(ne.lat, ne.lng);
        var cadSW = wgs84ToCassini(sw.lat, sw.lng);

        var pNW = toScreen(cadNW.e, cadNW.n, padding, baseScale, minE, minN);
        var pNE = toScreen(cadNE.e, cadNE.n, padding, baseScale, minE, minN);
        var pSW = toScreen(cadSW.e, cadSW.n, padding, baseScale, minE, minN);

        var m11 = (pNE.x - pNW.x) / 256;
        var m12 = (pNE.y - pNW.y) / 256;
        var m21 = (pSW.x - pNW.x) / 256;
        var m22 = (pSW.y - pNW.y) / 256;
        var dx = pNW.x;
        var dy = pNW.y;

        ctx.save();
        ctx.setTransform(m11, m12, m21, m22, dx, dy);
        ctx.drawImage(img, 0, 0, 256, 256);
        ctx.restore();
      }
    }
  }

  ctx.restore();
}

/* --- UI Helpers --- */
function showToast(message, type) {
  var toast = document.getElementById('globalToast');
  if (!toast) return;
  if (toastTimer) clearTimeout(toastTimer);

  toast.innerText = message;
  toast.style.borderColor = (type === 'warning' || type === 'error') ? '#ff3344' : '#00f2ff';
  toast.style.color = (type === 'warning' || type === 'error') ? '#ff5566' : '#ffffff';
  toast.style.display = 'block';

  toastTimer = setTimeout(function() {
    toast.style.display = 'none';
  }, 3500);
}

function toggleDropdown(e, menuId) {
  if (e) e.stopPropagation();
  var menu = document.getElementById(menuId);
  var isAlreadyOpen = menu.classList.contains('show');
  document.querySelectorAll('.dropdown-menu').forEach(m => m.classList.remove('show'));
  if (!isAlreadyOpen) menu.classList.add('show');
}

window.addEventListener('click', function(e) {
  if (!e.target.closest('.dropdown-container')) {
    document.querySelectorAll('.dropdown-menu').forEach(m => m.classList.remove('show'));
  }
});

function setupResizableSidebar() {
  var sidebar = document.getElementById('controlsSidebar');
  var resizer = document.getElementById('dragResizer');
  var isResizing = false;

  resizer.addEventListener('mousedown', function(e) {
    isResizing = true;
    resizer.classList.add('resizing');
    document.body.style.cursor = 'col-resize';
    document.body.style.userSelect = 'none';
  });

  window.addEventListener('mousemove', function(e) {
    if (!isResizing) return;
    var newWidth = e.clientX;
    if (newWidth >= 280 && newWidth <= 600) {
      sidebar.style.width = newWidth + 'px';
      sidebar.style.minWidth = newWidth + 'px';
      resizeCanvas();
      drawCAD();
    }
  });

  window.addEventListener('mouseup', function() {
    if (isResizing) {
      isResizing = false;
      resizer.classList.remove('resizing');
      document.body.style.cursor = '';
      document.body.style.userSelect = '';
      resizeCanvas();
      drawCAD();
    }
  });
}

function setupDragAndDrop() {
  var dropZone = document.getElementById('dropZone');

  ['dragenter', 'dragover', 'dragleave', 'drop'].forEach(eventName => {
    dropZone.addEventListener(eventName, preventDefaults, false);
  });

  function preventDefaults(e) { e.preventDefault(); e.stopPropagation(); }

  ['dragenter', 'dragover'].forEach(eventName => {
    dropZone.addEventListener(eventName, () => dropZone.classList.add('drag-over'), false);
  });

  ['dragleave', 'drop'].forEach(eventName => {
    dropZone.addEventListener(eventName, () => dropZone.classList.remove('drag-over'), false);
  });

  dropZone.addEventListener('drop', function(e) {
    var files = e.dataTransfer.files;
    if (files.length > 0) {
      Array.from(files).forEach(f => processFile(f));
    }
  });
}

function handleFileSelect(e) {
  var files = e.target.files;
  if (files.length > 0) {
    Array.from(files).forEach(f => processFile(f));
  }
  e.target.value = '';
}

function processFile(file) {
  var reader = new FileReader();
  reader.onload = function(e) {
    var currentVal = document.getElementById('importPasteArea').value;
    if (currentVal && currentVal.trim().length > 0) {
      document.getElementById('importPasteArea').value = currentVal.trim() + "\n\n" + e.target.result;
    } else {
      document.getElementById('importPasteArea').value = e.target.result;
    }
    showToast(`Loaded "${file.name}". Click "Process Data" to import.`, "info");
  };
  reader.readAsText(file);
}

function parseAndImportData() {
  var rawText = document.getElementById('importPasteArea').value.trim();
  if (!rawText) {
    showToast("Please choose a file or paste data into the text box first!", "warning");
    return;
  }

  pushState();

  var lines = rawText.split(/\r?\n/);
  var bRecords = [];
  var dRecords = [];
  var fixPoints = [];

  lines.forEach(function(line) {
    var trimmed = line.trim();
    if (!trimmed || trimmed.startsWith('#')) return; 

    var parts = trimmed.split(/\s+/);
    var code = parts[0].toUpperCase();

    if (code === 'C' && parts.length >= 4) {
      var stnId = parts[1];
      var easting = parseFloat(parts[2]);
      var northing = parseFloat(parts[3]);
      if (!isNaN(easting) && !isNaN(northing)) {
        var existingFix = fixPoints.find(p => p.id === stnId);
        if (!existingFix) {
          fixPoints.push({ id: stnId, e: easting, n: northing });
        }
      }
    } 
    else if (code === 'B' && parts.length >= 3) {
      var stnPair = parts[1].split('-');
      if (stnPair.length === 2) {
        bRecords.push({ from: stnPair[0], to: stnPair[1], dmsStr: parts[2] });
      }
    } 
    else if (code === 'D' && parts.length >= 3) {
      var stnPairD = parts[1].split('-');
      if (stnPairD.length === 2) {
        dRecords.push({ from: stnPairD[0], to: stnPairD[1], dist: parseFloat(parts[2]) });
      }
    }
  });

  if (bRecords.length === 0 && dRecords.length === 0) {
    lines.forEach(function(line) {
      var parts = line.trim().split(/[\s,]+/);
      if (parts.length >= 4) {
        bRecords.push({ from: parts[0], to: parts[1], dmsStr: parts[2] });
        dRecords.push({ from: parts[0], to: parts[1], dist: parseFloat(parts[3]) });
      }
    });
  }

  if (bRecords.length === 0 && fixPoints.length === 0) {
    showToast("Could not parse valid line or station records. Please check file content.", "warning");
    return;
  }

  if (fixPoints.length > 0) {
    fixPoints.forEach(p => {
      var existing = points.find(pt => pt.id === p.id);
      if (existing) {
        existing.e = p.e;
        existing.n = p.n;
      } else {
        points.push({ id: p.id, e: p.e, n: p.n });
      }
      if (!datumPoints.includes(p.id)) {
        datumPoints.push(p.id);
      }
    });
    if (points.length === fixPoints.length) {
      document.getElementById('datumE').value = fixPoints[0].e.toFixed(3);
      document.getElementById('datumN').value = fixPoints[0].n.toFixed(3);
      document.getElementById('initialStn').value = fixPoints[0].id;
    }
  } else if (points.length === 0) {
    var baseE = parseFloat(document.getElementById('datumE').value) || 0;
    var baseN = parseFloat(document.getElementById('datumN').value) || 0;
    var initId = (bRecords.length > 0) ? bRecords[0].from : (document.getElementById('initialStn').value.trim() || '2');
    points.push({ id: initId, e: baseE, n: baseN });
    if (!datumPoints.includes(initId)) {
      datumPoints.push(initId);
    }
    document.getElementById('initialStn').value = initId;
  }

  var pad = n => String(n).padStart(2, '0');
  var initialLegCount = legs.length;

  var pairedRecords = [];
  bRecords.forEach(function(bRec) {
    var dRec = dRecords.find(d => (d.from === bRec.from && d.to === bRec.to) || (d.from === bRec.to && d.to === bRec.from));
    if (dRec) {
      pairedRecords.push({ bRec: bRec, dRec: dRec });
    }
  });

  var remaining = pairedRecords.slice();
  var maxPasses = 20;
  var pass = 0;
  var addedInPass = true;

  while (remaining.length > 0 && addedInPass && pass < maxPasses) {
    pass++;
    addedInPass = false;
    var nextRemaining = [];

    for (var i = 0; i < remaining.length; i++) {
      var item = remaining[i];
      var bRec = item.bRec;
      var dRec = item.dRec;

      var alreadyExists = legs.some(l => (l.from === bRec.from && l.to === bRec.to) || (l.from === bRec.to && l.to === bRec.from));
      if (alreadyExists) continue;

      var startPt = points.find(p => p.id === bRec.from);
      var targetPt = points.find(p => p.id === bRec.to);

      var dmsParts = bRec.dmsStr.split(/[-°'"]/);
      var deg = parseInt(dmsParts[0] || '0', 10);
      var min = parseInt(dmsParts[1] || '0', 10);
      var sec = parseInt(dmsParts[2] || '0', 10);

      var decDeg = deg + (min / 60) + (sec / 3600);
      var rad = decDeg * (Math.PI / 180);

      var dE = dRec.dist * Math.sin(rad);
      var dN = dRec.dist * Math.cos(rad);

      if (startPt) {
        var calcE = startPt.e + dE;
        var calcN = startPt.n + dN;

        if (!targetPt) {
          targetPt = { id: bRec.to, e: calcE, n: calcN };
          points.push(targetPt);
        }

        legs.push({
          from: bRec.from,
          to: bRec.to,
          deg: deg, min: min, sec: sec,
          dmsFormatted: `${deg}-${pad(min)}-${pad(sec)}`,
          dist: dRec.dist,
          rawDist: dRec.dist,
          rawUnit: 'm',
          p1: startPt,
          p2: targetPt
        });
        addedInPass = true;
      } else if (targetPt) {
        var calcE = targetPt.e - dE;
        var calcN = targetPt.n - dN;

        startPt = { id: bRec.from, e: calcE, n: calcN };
        points.push(startPt);

        legs.push({
          from: bRec.from,
          to: bRec.to,
          deg: deg, min: min, sec: sec,
          dmsFormatted: `${deg}-${pad(min)}-${pad(sec)}`,
          dist: dRec.dist,
          rawDist: dRec.dist,
          rawUnit: 'm',
          p1: startPt,
          p2: targetPt
        });
        addedInPass = true;
      } else {
        nextRemaining.push(item);
      }
    }
    remaining = nextRemaining;
  }

  var addedLegsCount = legs.length - initialLegCount;
  if (legs.length > 0) {
    var lastLeg = legs[legs.length - 1];
    document.getElementById('fromStn').value = lastLeg.to;
    document.getElementById('toStn').value = getNextStationId(lastLeg.to);
  }

  updateLineLogDropdowns();
  updateTable();
  updateStnTable();
  updateUndoRedoUI();
  switchTab('entry'); 
  zoomExtents();
  showToast(`Merged file data: added ${addedLegsCount} new line(s). Total lines: ${legs.length}`, "success");
}

function addOrUpdateFixPoint() {
  var stnId = document.getElementById('initialStn').value.trim();
  var eVal = parseFloat(document.getElementById('datumE').value);
  var nVal = parseFloat(document.getElementById('datumN').value);

  if (!stnId || isNaN(eVal) || isNaN(nVal)) {
    showToast("Please enter a valid Station ID, Easting, and Northing coordinates.", "warning");
    return;
  }

  pushState();

  var existingPt = points.find(p => p.id.toLowerCase() === stnId.toLowerCase());
  if (existingPt) {
    existingPt.e = eVal;
    existingPt.n = nVal;
    if (!datumPoints.includes(existingPt.id)) datumPoints.push(existingPt.id);
  } else {
    points.push({ id: stnId, e: eVal, n: nVal });
    datumPoints.push(stnId);
  }

  document.getElementById('fromStn').value = stnId;
  document.getElementById('toStn').value = getNextStationId(stnId);

  recomputeTraverseChain();
  updateStnTable();
  zoomExtents();
  showToast(`🔺 Station ${stnId} set as Fix Point (E: ${eVal.toFixed(3)}, N: ${nVal.toFixed(3)})`, "success");
}

function openDatumModal(stnId) {
  var pt = points.find(p => p.id === stnId);
  if (!pt) return;

  document.getElementById('datumStnId').value = pt.id;
  document.getElementById('datumStnDisplay').value = pt.id;
  document.getElementById('datumEastingInput').value = pt.e.toFixed(3);
  document.getElementById('datumNorthingInput').value = pt.n.toFixed(3);

  var isDatum = datumPoints.includes(pt.id);
  document.getElementById('removeDatumBtn').style.display = isDatum ? 'block' : 'none';
  document.getElementById('datumModal').style.display = 'flex';
}

function closeDatumModal() {
  document.getElementById('datumModal').style.display = 'none';
}

function saveDatumCoordinates() {
  var stnId = document.getElementById('datumStnId').value;
  var newE = parseFloat(document.getElementById('datumEastingInput').value);
  var newN = parseFloat(document.getElementById('datumNorthingInput').value);

  if (isNaN(newE) || isNaN(newN)) {
    showToast("Please enter valid numerical Easting and Northing coordinates.", "warning");
    return;
  }

  pushState();

  var pt = points.find(p => p.id === stnId);
  if (pt) {
    pt.e = newE;
    pt.n = newN;
    if (!datumPoints.includes(stnId)) datumPoints.push(stnId);
  }

  closeDatumModal();
  recomputeTraverseChain();
  updateStnTable();
  showToast(`Updated coordinates for Station ${stnId}.`, "success");
}

function removeSelectedDatum() {
  var stnId = document.getElementById('datumStnId').value;
  var idx = datumPoints.indexOf(stnId);
  
  if (idx !== -1) {
    pushState();
    datumPoints.splice(idx, 1);
    closeDatumModal();
    recomputeTraverseChain();
    updateStnTable();
    showToast(`Unset Fix status for Station ${stnId}.`, "info");
  }
}

function deleteStationFromDatumModal() {
  var stnId = document.getElementById('datumStnId').value;
  closeDatumModal();
  promptDeleteStation(stnId);
}

function promptDeleteStationFromToast() {
  if (!inspectedStationId) return;
  promptDeleteStation(inspectedStationId);
}

function promptDeleteStation(stnId) {
  var connectedLegs = legs.filter(l => l.from === stnId || l.to === stnId);
  var isFix = datumPoints.includes(stnId);

  document.getElementById('pendingDeleteStnId').value = stnId;
  var warningText = `Are you sure you want to delete ${isFix ? 'Fix Station 🔺' : 'Station ⭕'} <b>${stnId}</b>?<br><br>`;
  if (connectedLegs.length > 0) {
    warningText += `⚠️ This station is connected to <b>${connectedLegs.length} line(s)</b> in Line Log. Deleting it will also remove all connected lines.`;
  } else {
    warningText += `This station has no connected lines.`;
  }

  document.getElementById('deleteStnWarningBody').innerHTML = warningText;
  document.getElementById('deleteStnModal').style.display = 'flex';
}

function closeDeleteStnModal() {
  document.getElementById('pendingDeleteStnId').value = '';
  document.getElementById('deleteStnModal').style.display = 'none';
}

function confirmExecuteDeleteStation() {
  var stnId = document.getElementById('pendingDeleteStnId').value;
  if (!stnId) return;

  pushState();

  var ptIdx = points.findIndex(p => p.id === stnId);
  if (ptIdx !== -1) points.splice(ptIdx, 1);

  var datumIdx = datumPoints.indexOf(stnId);
  if (datumIdx !== -1) datumPoints.splice(datumIdx, 1);

  var removedLegsCount = 0;
  for (var i = legs.length - 1; i >= 0; i--) {
    if (legs[i].from === stnId || legs[i].to === stnId) {
      legs.splice(i, 1);
      removedLegsCount++;
    }
  }

  lotRecords.forEach(lot => {
    lot.nodes = lot.nodes.filter(id => id !== stnId);
  });

  closeDeleteStnModal();
  clearSelections();
  updateLineLogDropdowns();
  updateTable();
  updateStnTable();
  updateLotTable();
  updateUndoRedoUI();
  drawCAD();

  showToast(`Deleted Station ${stnId} ${removedLegsCount > 0 ? `and ${removedLegsCount} line(s)` : ''}.`, "info");
}

function onCrsChange() {
  var val = document.getElementById('crsSelect').value;
  var customBlock = document.getElementById('customGpsBlock');
  customBlock.style.display = (val === 'custom') ? 'block' : 'none';
  drawCAD();
}

var currentDataSubTab = 'lines';

/* --- Tab Switching (Updated with Calc Tab) --- */
function switchTab(tab) {
  if (tab === 'stn') {
    tab = 'data';
    switchDataSubTab('stns');
  }

  var entryTab = document.getElementById('tab-entry');
  var importTab = document.getElementById('tab-import');
  var dataTab = document.getElementById('tab-data');
  var lotTab = document.getElementById('tab-lot');
  var calcTab = document.getElementById('tab-calc');

  if (entryTab) entryTab.style.display = (tab === 'entry') ? 'block' : 'none';
  if (importTab) importTab.style.display = (tab === 'import') ? 'block' : 'none';
  if (dataTab) dataTab.style.display = (tab === 'data') ? 'block' : 'none';
  if (lotTab) lotTab.style.display = (tab === 'lot') ? 'block' : 'none';
  if (calcTab) calcTab.style.display = (tab === 'calc') ? 'block' : 'none';
  
  var btns = document.querySelectorAll('.tab-bar .tab-btn');
  if (btns.length > 0) btns[0].classList.toggle('active', tab === 'entry');
  if (btns.length > 1) btns[1].classList.toggle('active', tab === 'import');
  if (btns.length > 2) btns[2].classList.toggle('active', tab === 'data');
  if (btns.length > 3) btns[3].classList.toggle('active', tab === 'lot');
  if (btns.length > 4) btns[4].classList.toggle('active', tab === 'calc');

  if (tab === 'data') {
    updateLineLogDropdowns();
    updateTable();
    updateStnTable();
  } else if (tab === 'calc') {
    computeCurrentTraverseClosure();
  }
}

function switchDataSubTab(sub) {
  currentDataSubTab = sub;
  var isLines = (sub === 'lines');
  
  document.getElementById('data-subview-lines').style.display = isLines ? 'block' : 'none';
  document.getElementById('data-subview-stns').style.display = isLines ? 'none' : 'block';

  document.getElementById('subTabLinesBtn').classList.toggle('active', isLines);
  document.getElementById('subTabStnsBtn').classList.toggle('active', !isLines);

  if (isLines) {
    updateLineLogDropdowns();
    updateTable();
  } else {
    updateStnTable();
  }
}

function resizeCanvas() {
  canvas.width = parent.clientWidth;
  canvas.height = parent.clientHeight;
}

function openLotModal() {
  if (points.length < 3) {
    showToast("At least 3 survey stations are required to create a Lot boundary!", "warning");
    return;
  }
  document.getElementById('lotModal').style.display = 'flex';
}

function closeLotModal() {
  document.getElementById('lotModal').style.display = 'none';
}

function extractLotNoFromUpi(upiStr) {
  if (upiStr.length >= 10) {
    var rawNum = upiStr.substring(9); 
    var parsedInt = parseInt(rawNum, 10);
    return !isNaN(parsedInt) ? parsedInt.toString() : rawNum;
  }
  var lotNumMatch = upiStr.match(/(\d+)$/);
  return lotNumMatch ? parseInt(lotNumMatch[1], 10).toString() : upiStr;
}

function startLotSelection() {
  var pa = document.getElementById('lotPaInput').value.trim();
  var upi = document.getElementById('lotUpiInput').value.trim();

  if (!pa || !upi) {
    showToast("Please enter valid No. PA and UPI.", "warning");
    return;
  }

  var isDuplicateUpi = lotRecords.some(l => l.upi.toLowerCase() === upi.toLowerCase());
  if (isDuplicateUpi) {
    showToast(`Duplicate UPI error: UPI [${upi}] already exists!`, "warning");
    return;
  }

  activeLotPa = pa;
  activeLotUpi = upi;
  activeLotNodes = [];
  isLotCreationMode = true;

  closeLotModal();

  var banner = document.getElementById('pickBanner');
  banner.innerText = `📦 LOT [${activeLotPa} | ${activeLotUpi}]: CLICK STN NODES CLOCKWISE (CLICK START NODE AGAIN TO CLOSE)`;
  banner.style.display = 'block';
  canvas.classList.add('pick-cursor');
}

function toggleMeasureTool() {
  if (points.length < 2) {
    showToast("At least 2 logged stations are required to measure!", "warning");
    return;
  }
  isMeasureMode = !isMeasureMode;
  measurePoints = [];
  snappedPoint = null;
  var btn = document.getElementById('measureBtn');
  var banner = document.getElementById('pickBanner');

  if (isMeasureMode) {
    if (isAreaMode) toggleAreaTool();
    if (pickTargetField) togglePickMode(pickTargetField);
    if (isLotCreationMode) isLotCreationMode = false;
    btn.classList.add('active-tool');
    banner.innerText = "📐 MEASURE TOOL: CLICK FIRST STATION NODE";
    banner.style.display = 'block';
    canvas.classList.add('pick-cursor');
  } else {
    btn.classList.remove('active-tool');
    banner.style.display = 'none';
    canvas.classList.remove('pick-cursor');
    drawCAD();
  }
}

function toggleAreaTool() {
  if (points.length < 3) {
    showToast("At least 3 survey stations are required to calculate area!", "warning");
    return;
  }
  isAreaMode = !isAreaMode;
  areaPoints = [];
  snappedPoint = null;
  var btn = document.getElementById('areaMeasureBtn');
  var banner = document.getElementById('pickBanner');

  if (isAreaMode) {
    if (isMeasureMode) toggleMeasureTool();
    if (pickTargetField) togglePickMode(pickTargetField);
    if (isLotCreationMode) isLotCreationMode = false;
    btn.classList.add('active-tool');
    banner.innerText = "📐 AREA TOOL: CLICK STATION NODES AROUND BOUNDARY (CLICK START TO CLOSE)";
    banner.style.display = 'block';
    canvas.classList.add('pick-cursor');
  } else {
    btn.classList.remove('active-tool');
    banner.style.display = 'none';
    canvas.classList.remove('pick-cursor');
    drawCAD();
  }
}

function togglePickMode(target) {
  if (points.length === 0) {
    showToast("No stations available in drawing to pick! Please add a Fix Point first.", "warning");
    return;
  }

  if (isMeasureMode) toggleMeasureTool();
  if (isAreaMode) toggleAreaTool();
  if (isLotCreationMode) isLotCreationMode = false;
  snappedPoint = null;

  var fromBtn = document.getElementById('pickFromBtn');
  var toBtn = document.getElementById('pickToBtn');
  var datumBtn = document.getElementById('pickDatumBtn');
  var banner = document.getElementById('pickBanner');

  if (pickTargetField === target) {
    pickTargetField = null;
    fromBtn.classList.remove('active-pick');
    toBtn.classList.remove('active-pick');
    datumBtn.classList.remove('active-pick');
    banner.style.display = 'none';
    canvas.classList.remove('pick-cursor');
  } else {
    pickTargetField = target;
    fromBtn.classList.toggle('active-pick', target === 'from');
    toBtn.classList.toggle('active-pick', target === 'to');
    datumBtn.classList.toggle('active-pick', target === 'datum');
    banner.innerText = `🎯 CLICK ANY STATION NODE TO ${target === 'datum' ? 'CONFIGURE FIX COORDINATES' : 'SELECT ' + target.toUpperCase() + ' STN'}`;
    banner.style.display = 'block';
    canvas.classList.add('pick-cursor');
  }
}

function setupCanvasListeners() {
  canvas.addEventListener('contextmenu', e => e.preventDefault()); 

  canvas.addEventListener('wheel', function(e) {
    e.preventDefault();
    var rect = canvas.getBoundingClientRect();
    var mouseX = e.clientX - rect.left;
    var mouseY = e.clientY - rect.top;

    var zoomIntensity = 0.15;
    var zoom = e.deltaY < 0 ? (1 + zoomIntensity) : (1 - zoomIntensity);
    if (zoomFactor * zoom < 0.05 || zoomFactor * zoom > 100) return;

    panX = mouseX - (mouseX - panX) * zoom;
    panY = mouseY - (mouseY - panY) * zoom;
    zoomFactor *= zoom;

    drawCAD();
  }, { passive: false });

  canvas.addEventListener('mousedown', function(e) {
    var rect = canvas.getBoundingClientRect();
    var mouseX = e.clientX - rect.left;
    var mouseY = e.clientY - rect.top;

    if (e.button === 1) { // Middle click pan
      e.preventDefault();
      isPanning = true;
      panStart = { x: e.clientX - panX, y: e.clientY - panY };
      canvas.classList.add('panning');
      return;
    }

    if (e.button === 0) { // Left click
      isBoxSelecting = true;
      hasDraggedBox = false;
      boxStart = { x: mouseX, y: mouseY };
      boxCurrent = { x: mouseX, y: mouseY };
    }
  });

  window.addEventListener('mousemove', function(e) {
    var rect = canvas.getBoundingClientRect();
    var mouseX = e.clientX - rect.left;
    var mouseY = e.clientY - rect.top;

    if (isPanning) {
      panX = e.clientX - panStart.x;
      panY = e.clientY - panStart.y;
      drawCAD();
      return;
    }

    if (isBoxSelecting) {
      if (Math.abs(mouseX - boxStart.x) > 4 || Math.abs(mouseY - boxStart.y) > 4) {
        hasDraggedBox = true;
      }
      boxCurrent = { x: mouseX, y: mouseY };
      drawCAD();
      return;
    }

    if (pickTargetField || isLotCreationMode || isMeasureMode || isAreaMode) {
      snappedPoint = findNearestStationNode(mouseX, mouseY, 20);
      drawCAD();
    } else {
      if (snappedPoint) {
        snappedPoint = null;
        drawCAD();
      }
    }
  });

  window.addEventListener('mouseup', function(e) { 
    if (isPanning) {
      isPanning = false;
      canvas.classList.remove('panning');
      return;
    }

    if (isBoxSelecting) {
      isBoxSelecting = false;
      if (hasDraggedBox) {
        finishAutoCadBoxSelection();
      } else {
        var rect = canvas.getBoundingClientRect();
        var clickX = e.clientX - rect.left;
        var clickY = e.clientY - rect.top;

        if (clickX >= 0 && clickX <= canvas.width && clickY >= 0 && clickY <= canvas.height) {
          handleCanvasClick(clickX, clickY);
        }
      }
    }
  });

  canvas.addEventListener('dblclick', zoomExtents);
}

function finishAutoCadBoxSelection() {
  if (!boxStart || !boxCurrent) return;

  var rx = Math.min(boxStart.x, boxCurrent.x);
  var ry = Math.min(boxStart.y, boxCurrent.y);
  var rw = Math.abs(boxCurrent.x - boxStart.x);
  var rh = Math.abs(boxCurrent.y - boxStart.y);

  var isWindowSelect = boxCurrent.x >= boxStart.x; 
  var isCrossingSelect = boxCurrent.x < boxStart.x; 

  if (rw < 5 && rh < 5) return;
  if (points.length === 0 || legs.length === 0) return;

  var minE = Math.min(...points.map(p => p.e));
  var maxE = Math.max(...points.map(p => p.e));
  var minN = Math.min(...points.map(p => p.n));
  var maxN = Math.max(...points.map(p => p.n));

  var rangeE = (maxE - minE) || 50;
  var rangeN = (maxN - minN) || 50;

  var padding = 120;
  var baseScale = Math.min((canvas.width - padding * 2) / rangeE, (canvas.height - padding * 2) / rangeN);

  selectedLegIndices = [];

  legs.forEach((leg, idx) => {
    var p1 = toScreen(leg.p1.e, leg.p1.n, padding, baseScale, minE, minN);
    var p2 = toScreen(leg.p2.e, leg.p2.n, padding, baseScale, minE, minN);

    var p1Inside = (p1.x >= rx && p1.x <= rx + rw && p1.y >= ry && p1.y <= ry + rh);
    var p2Inside = (p2.x >= rx && p2.x <= rx + rw && p2.y >= ry && p2.y <= ry + rh);

    if (isWindowSelect) {
      if (p1Inside && p2Inside) selectedLegIndices.push(idx);
    } else if (isCrossingSelect) {
      var midX = (p1.x + p2.x) / 2;
      var midY = (p1.y + p2.y) / 2;
      var midInside = (midX >= rx && midX <= rx + rw && midY >= ry && midY <= ry + rh);
      if (p1Inside || p2Inside || midInside) selectedLegIndices.push(idx);
    }
  });

  var toast = document.getElementById('inspectorToast');
  var deleteBtn = document.getElementById('toastDeleteMultiBtn');

  if (selectedLegIndices.length > 0) {
    selectedLegIndex = selectedLegIndices[0];
    document.getElementById('toastTitle').innerText = isWindowSelect ? `📦 Window Selection` : `✂️ Crossing Selection`;
    document.getElementById('toastBody').innerHTML = `Selected Lines: <b>${selectedLegIndices.length} items</b>`;
    deleteBtn.style.display = 'block';
    deleteBtn.innerText = `🗑️ Delete ${selectedLegIndices.length} Selected Lines`;
    document.getElementById('toastDatumBtn').style.display = 'none';
    toast.style.display = 'block';
  } else {
    toast.style.display = 'none';
    deleteBtn.style.display = 'none';
  }

  boxStart = null;
  boxCurrent = null;
  drawCAD();
}

function clearSelections() {
  selectedLegIndex = null;
  selectedLegIndices = [];
  selectedLotIndex = null;
  snappedPoint = null;
  inspectedStationId = null;
  document.getElementById('inspectorToast').style.display = 'none';
  document.getElementById('toastDeleteMultiBtn').style.display = 'none';
  updateTableHighlight();
  updateLotTableHighlight();
  drawCAD();
}

function deleteSelectedMultiLegs() {
  if (selectedLegIndices.length === 0) return;

  pushState();
  selectedLegIndices.sort((a, b) => b - a);
  selectedLegIndices.forEach(idx => {
    legs.splice(idx, 1);
  });

  var deletedCount = selectedLegIndices.length;
  clearSelections();
  updateTable();
  updateUndoRedoUI();
  drawCAD();
  showToast(`Deleted ${deletedCount} selected line(s).`, "info");
}

function findNearestStationNode(clickX, clickY, maxRadius) {
  if (points.length === 0) return null;

  var minE = Math.min(...points.map(p => p.e));
  var maxE = Math.max(...points.map(p => p.e));
  var minN = Math.min(...points.map(p => p.n));
  var maxN = Math.max(...points.map(p => p.n));

  var rangeE = (maxE - minE) || 50;
  var rangeN = (maxN - minN) || 50;

  var padding = 120;
  var baseScale = Math.min((canvas.width - padding * 2) / rangeE, (canvas.height - padding * 2) / rangeN);

  var nearestPt = null;
  var minDist = maxRadius || 20;

  for (var i = 0; i < points.length; i++) {
    var pt = points[i];
    var scrX = (padding + (pt.e - minE) * baseScale) * zoomFactor + panX;
    var scrY = (canvas.height - (padding + (pt.n - minN) * baseScale)) * zoomFactor + panY;

    var d = Math.hypot(clickX - scrX, clickY - scrY);
    if (d <= minDist) {
      minDist = d;
      nearestPt = pt;
    }
  }
  return nearestPt;
}

function handleCanvasClick(clickX, clickY) {
  if (points.length === 0) return;

  var toast = document.getElementById('inspectorToast');
  var foundPoint = snappedPoint || findNearestStationNode(clickX, clickY, 16);
  var foundLegIndex = null;
  var foundLotIndex = null;

  selectedLegIndices = [];
  document.getElementById('toastDeleteMultiBtn').style.display = 'none';

  var minE = Math.min(...points.map(p => p.e));
  var maxE = Math.max(...points.map(p => p.e));
  var minN = Math.min(...points.map(p => p.n));
  var maxN = Math.max(...points.map(p => p.n));

  var rangeE = (maxE - minE) || 50;
  var rangeN = (maxN - minN) || 50;

  var padding = 120;
  var baseScale = Math.min((canvas.width - padding * 2) / rangeE, (canvas.height - padding * 2) / rangeN);

  if (!foundPoint && legs.length > 0) {
    for (var j = 0; j < legs.length; j++) {
      var leg = legs[j];
      var p1 = toScreen(leg.p1.e, leg.p1.n, padding, baseScale, minE, minN);
      var p2 = toScreen(leg.p2.e, leg.p2.n, padding, baseScale, minE, minN);

      var lineDist = distToSegment({x: clickX, y: clickY}, p1, p2);
      if (lineDist <= 8) {
        foundLegIndex = j;
        break;
      }
    }
  }

  if (!foundPoint && foundLegIndex === null && lotRecords.length > 0) {
    for (var l = 0; l < lotRecords.length; l++) {
      var lot = lotRecords[l];
      var poly = [];
      lot.nodes.forEach(stnId => {
        var p = points.find(pt => pt.id === stnId);
        if (p) poly.push(toScreen(p.e, p.n, padding, baseScale, minE, minN));
      });

      if (poly.length >= 3 && isPointInPolygon({x: clickX, y: clickY}, poly)) {
        foundLotIndex = l;
        break;
      }
    }
  }

  if (foundPoint) {
    if (pickTargetField === 'datum') {
      togglePickMode('datum');
      openDatumModal(foundPoint.id);
      return;
    }

    if (isLotCreationMode) {
      if (activeLotNodes.length >= 3 && foundPoint.id === activeLotNodes[0]) {
        activeLotNodes.push(foundPoint.id);
        var lotDisplayNo = extractLotNoFromUpi(activeLotUpi);

        lotRecords.push({
          pa: activeLotPa,
          upi: activeLotUpi,
          lotNo: lotDisplayNo,
          nodes: JSON.parse(JSON.stringify(activeLotNodes))
        });

        isLotCreationMode = false;
        snappedPoint = null;
        document.getElementById('pickBanner').style.display = 'none';
        canvas.classList.remove('pick-cursor');

        updateLotTable();
        switchTab('lot');
        drawCAD();
        showToast(`Lot Stn [${activeLotPa} | Lot ${lotDisplayNo}] created successfully!`, "success");
        return;
      }

      activeLotNodes.push(foundPoint.id);
      var banner = document.getElementById('pickBanner');
      banner.innerText = `📦 LOT [${activeLotPa}]: ADDED STN ${foundPoint.id} (COUNT: ${activeLotNodes.length}). CLICK START NODE (${activeLotNodes[0]}) TO CLOSE`;
      drawCAD();
      return;
    }

    if (isAreaMode) {
      if (areaPoints.length >= 3 && foundPoint.id === areaPoints[0].id) {
        var geom = computePolygonAreaAndPerimeter(areaPoints);
        document.getElementById('toastTitle').innerText = "📐 ENCLOSED BOUNDARY AREA";
        document.getElementById('toastBody').innerHTML = 
          `Nodes: <b>${areaPoints.map(p => p.id).join(' ➔ ')}</b><br>` +
          `Area (m²): <b>${geom.areaSqM.toFixed(3)} m²</b><br>` +
          `Area (Hectares): <b>${geom.areaHa.toFixed(4)} ha</b><br>` +
          `Area (Acres): <b>${geom.areaAc.toFixed(4)} ac</b><br>` +
          `Perimeter: <b>${geom.perimeterM.toFixed(3)} m</b>`;
        toast.style.display = 'block';
        toggleAreaTool();
        return;
      }

      areaPoints.push(foundPoint);
      var bnr = document.getElementById('pickBanner');
      bnr.innerText = `📐 AREA TOOL: ADDED STN ${foundPoint.id} (COUNT: ${areaPoints.length}). ${areaPoints.length >= 3 ? 'CLICK START TO CLOSE & COMPUTE' : 'CLICK NEXT NODE'}`;
      drawCAD();
      return;
    }

    if (isMeasureMode) {
      measurePoints.push(foundPoint);
      var banner = document.getElementById('pickBanner');
      
      if (measurePoints.length === 1) {
        banner.innerText = `📐 POINT 1: ${foundPoint.id} SELECTED. CLICK SECOND NODE`;
      } else if (measurePoints.length === 2) {
        var p1 = measurePoints[0];
        var p2 = measurePoints[1];

        var dE = p2.e - p1.e;
        var dN = p2.n - p1.n;
        
        var distanceM = Math.hypot(dE, dN);
        var distanceLk = distanceM / LINK_TO_METER;

        var rad = Math.atan2(dE, dN);
        var decDeg = rad * (180 / Math.PI);
        if (decDeg < 0) decDeg += 360;

        var deg = Math.floor(decDeg);
        var remMin = (decDeg - deg) * 60;
        var min = Math.floor(remMin);
        var sec = Math.round((remMin - min) * 60);

        var pad = n => String(n).padStart(2, '0');
        var dmsStr = `${deg}°${pad(min)}'${pad(sec)}"`;

        document.getElementById('toastTitle').innerText = "📐 INVERSE MEASUREMENT";
        document.getElementById('toastBody').innerHTML = 
          `From: <b>${p1.id}</b> ➔ To: <b>${p2.id}</b><br>` +
          `Bearing: <b>${dmsStr}</b><br>` +
          `Dist (m): <b>${distanceM.toFixed(3)} m</b><br>` +
          `Dist (lk): <b>${distanceLk.toFixed(2)} lk</b>`;
        toast.style.display = 'block';

        drawCAD();
        
        var scrP1 = toScreen(p1.e, p1.n, padding, baseScale, minE, minN);
        var scrP2 = toScreen(p2.e, p2.n, padding, baseScale, minE, minN);

        ctx.strokeStyle = '#ffea00';
        ctx.lineWidth = 2.5;
        ctx.setLineDash([6, 4]);
        ctx.beginPath();
        ctx.moveTo(scrP1.x, scrP1.y);
        ctx.lineTo(scrP2.x, scrP2.y);
        ctx.stroke();
        ctx.setLineDash([]);

        toggleMeasureTool();
      }
    } else if (pickTargetField) {
      if (pickTargetField === 'from') {
        document.getElementById('fromStn').value = foundPoint.id;
        var nextId = getNextStationId(foundPoint.id);
        
        if (points.some(p => p.id === nextId)) {
          var numericIds = points.map(p => {
            var m = p.id.match(/\d+$/);
            return m ? parseInt(m[0], 10) : 0;
          }).filter(n => !isNaN(n));

          if (numericIds.length > 0) {
            var maxNum = Math.max(...numericIds);
            var sampleMatch = foundPoint.id.match(/^(.*?)(\d+)$/);
            var prefix = sampleMatch ? sampleMatch[1] : '';
            var numLen = sampleMatch ? sampleMatch[2].length : 1;
            nextId = prefix + (maxNum + 1).toString().padStart(numLen, '0');
          }
        }
        document.getElementById('toStn').value = nextId;
      } else if (pickTargetField === 'to') {
        document.getElementById('toStn').value = foundPoint.id;
      }
      togglePickMode(pickTargetField);
    } else {
      var gps = getWGS84Coords(foundPoint.e, foundPoint.n);
      var isDatum = datumPoints.includes(foundPoint.id);
      inspectedStationId = foundPoint.id;
      
      document.getElementById('toastTitle').innerText = (isDatum ? "🔺 FIX STN: " : "STN: ") + foundPoint.id;
      document.getElementById('toastBody').innerHTML = 
        `Easting (X): <b>${foundPoint.e.toFixed(3)}</b><br>` +
        `Northing (Y): <b>${foundPoint.n.toFixed(3)}</b><br>` +
        `GPS Latitude: <b>${gps.lat.toFixed(6)}°</b><br>` +
        `GPS Longitude: <b>${gps.lng.toFixed(6)}°</b><br>` +
        `Node Status: <b style="color: ${isDatum ? '#ffea00' : '#00f2ff'}">${isDatum ? 'FIX POINT 🔺' : 'STANDARD STN ⭕'}</b>`;

      var datumBtn = document.getElementById('toastDatumBtn');
      datumBtn.style.display = 'block';
      datumBtn.onclick = function() { openDatumModal(foundPoint.id); };
      datumBtn.innerText = isDatum ? "Edit Fix Coordinates" : "Set as Fix Point";

      var deleteStnBtn = document.getElementById('toastDeleteStnBtn');
      if (deleteStnBtn) deleteStnBtn.style.display = 'block';

      toast.style.display = 'block';

      var lotIdx = lotRecords.findIndex(l => l.nodes.includes(foundPoint.id));
      selectedLotIndex = (lotIdx !== -1) ? lotIdx : null;
      if (selectedLotIndex !== null) updateLotTableHighlight();
      drawCAD();
    }
  } else if (foundLegIndex !== null) {
    selectLegRecord(foundLegIndex, true);
  } else if (foundLotIndex !== null) {
    selectLotRecord(foundLotIndex, true);
  } else {
    clearSelections();
    if (pickTargetField) togglePickMode(pickTargetField);
    if (isMeasureMode) toggleMeasureTool();
    if (isAreaMode) toggleAreaTool();
    if (isLotCreationMode) {
      isLotCreationMode = false;
      document.getElementById('pickBanner').style.display = 'none';
      canvas.classList.remove('pick-cursor');
    }
  }
}

function selectLotRecord(lotIdx, switchTabFlag) {
  selectedLotIndex = lotIdx;
  updateLotTableHighlight();
  drawCAD();

  var selectedLot = lotRecords[lotIdx];
  if (selectedLot) {
    var lotPts = [];
    selectedLot.nodes.forEach(stnId => {
      var pt = points.find(p => p.id === stnId);
      if (pt) lotPts.push(pt);
    });

    var geom = computePolygonAreaAndPerimeter(lotPts);
    var toast = document.getElementById('inspectorToast');
    document.getElementById('toastTitle').innerText = `Lot ${selectedLot.lotNo}`;
    document.getElementById('toastBody').innerHTML = 
      `PA No: <b>${selectedLot.pa}</b><br>` +
      `UPI: <b>${selectedLot.upi}</b><br>` +
      `Area (m²): <b>${geom.areaSqM.toFixed(3)} m²</b><br>` +
      `Area (ha): <b>${geom.areaHa.toFixed(4)} ha</b><br>` +
      `Area (ac): <b>${geom.areaAc.toFixed(4)} ac</b><br>` +
      `Perimeter: <b>${geom.perimeterM.toFixed(3)} m</b><br>` +
      `Node Count: <b>${selectedLot.nodes.length - 1} Vertices</b>`;
    document.getElementById('toastDatumBtn').style.display = 'none';
    toast.style.display = 'block';
  }

  if (switchTabFlag) {
    switchTab('lot');
    var row = document.getElementById(`lotRow_${lotIdx}_0`);
    if (row) row.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  }
}

function updateLotTableHighlight() {
  var rows = document.querySelectorAll('#lotTable tbody tr');
  rows.forEach((row) => {
    var idx = parseInt(row.getAttribute('data-lot-idx'), 10);
    row.classList.toggle('selected-row', idx === selectedLotIndex);
  });
}

function isPointInPolygon(point, vs) {
  var x = point.x, y = point.y;
  var inside = false;
  for (var i = 0, j = vs.length - 1; i < vs.length; j = i++) {
    var xi = vs[i].x, yi = vs[i].y;
    var xj = vs[j].x, yj = vs[j].y;
    var intersect = ((yi > y) !== (yj > y)) && (x < (xj - xi) * (y - yi) / (yj - yi) + xi);
    if (intersect) inside = !inside;
  }
  return inside;
}

function distToSegment(p, v, w) {
  var l2 = Math.pow(v.x - w.x, 2) + Math.pow(v.y - w.y, 2);
  if (l2 === 0) return Math.hypot(p.x - v.x, p.y - v.y);
  var t = ((p.x - v.x) * (w.x - v.x) + (p.y - v.y) * (w.y - v.y)) / l2;
  t = Math.max(0, Math.min(1, t));
  return Math.hypot(p.x - (v.x + t * (w.x - v.x)), p.y - (v.y + t * (w.y - v.y)));
}

function selectLegRecord(index, switchTabFlag) {
  selectedLegIndex = index;
  selectedLegIndices = [index];
  updateTableHighlight();
  drawCAD();

  if (switchTabFlag) {
    switchTab('data');
    var row = document.getElementById(`legRow_${index}`);
    if (row) row.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  }
}

function updateTableHighlight() {
  var rows = document.querySelectorAll('#traverseTable tbody tr');
  rows.forEach((row, i) => {
    row.classList.toggle('selected-row', i === selectedLegIndex || selectedLegIndices.includes(i));
  });
}

function toScreen(e, n, padding, baseScale, minE, minN) {
  return {
    x: (padding + (e - minE) * baseScale) * zoomFactor + panX,
    y: (canvas.height - (padding + (n - minN) * baseScale)) * zoomFactor + panY
  };
}

/* --- Coordinate Transformation (Cassini Soldner <--> WGS84) --- */
const CASSINI_STATE_ORIGINS = {
  "johor_kertau":      { lat: 2.0425, lng: 103.5627583, e0: 0.0, n0: 0.0, a: 6377304.063, f: 1/300.8017 },
  "n9_kertau":         { lat: 2.712283333, lng: 101.9411667, e0: -242.0048934, n0: -948.546528, a: 6377304.063, f: 1/300.8017 },
  "pahang_kertau":     { lat: 3.710972222, lng: 102.4361778, e0: 0.0, n0: 0.0, a: 6377304.063, f: 1/300.8017 },
  "selangor_kertau":   { lat: 3.680344444, lng: 101.5082444, e0: -21759.43848, n0: 55960.90576, a: 6377304.063, f: 1/300.8017 },
  "kelantan_kertau":   { lat: 5.893922222, lng: 102.1772917, e0: 0.0, n0: 0.0, a: 6377304.063, f: 1/300.8017 },
  "terengganu_kertau": { lat: 4.946141667, lng: 102.8952083, e0: 0.0, n0: 0.0, a: 6377304.063, f: 1/300.8017 },
  "perak_kertau":      { lat: 4.859380556, lng: 100.8167667, e0: 0.0, n0: 133453.6688, a: 6377304.063, f: 1/300.8017 },
  "penang_kertau":     { lat: 5.421325, lng: 100.3458694, e0: 0.0, n0: 0.0, a: 6377304.063, f: 1/300.8017 },
  "kedah_kertau":      { lat: 5.965147222, lng: 100.6375944, e0: 0.0, n0: 0.0, a: 6377304.063, f: 1/300.8017 },

  "johor_gdm2000":     { lat: 2.0425561000, lng: 103.5610659167, e0: 0.0, n0: 0.0, a: 6378137.0, f: 1/298.257222101 },
  "n9_gdm2000":        { lat: 2.7121205083, lng: 101.9397026917, e0: 0.0, n0: 0.0, a: 6378137.0, f: 1/298.257222101 },
  "pahang_gdm2000":    { lat: 3.7107479528, lng: 102.4346132556, e0: 0.0, n0: 0.0, a: 6378137.0, f: 1/298.257222101 },
  "selangor_gdm2000":  { lat: 3.6801049389, lng: 101.5068016139, e0: 0.0, n0: 0.0, a: 6378137.0, f: 1/298.257222101 },
  "terengganu_gdm2000":{ lat: 4.9458255111, lng: 102.8936124889, e0: 0.0, n0: 0.0, a: 6378137.0, f: 1/298.257222101 },
  "penang_gdm2000":    { lat: 5.4208900917, lng: 100.3446556222, e0: 0.0, n0: 0.0, a: 6378137.0, f: 1/298.257222101 },
  "kedah_gdm2000":     { lat: 5.9646726528, lng: 100.6363718333, e0: 0.0, n0: 0.0, a: 6378137.0, f: 1/298.257222101 },
  "perak_gdm2000":     { lat: 4.8590680222, lng: 100.8154084389, e0: 0.0, n0: 0.0, a: 6378137.0, f: 1/298.257222101 },
  "kelantan_gdm2000":  { lat: 5.8936332639, lng: 102.1756236917, e0: 0.0, n0: 0.0, a: 6378137.0, f: 1/298.257222101 }
};

function getCrsOrigin() {
  var crsKey = document.getElementById('crsSelect') ? document.getElementById('crsSelect').value : 'johor_gdm2000';
  var origin = CASSINI_STATE_ORIGINS[crsKey] || CASSINI_STATE_ORIGINS["johor_gdm2000"];
  if (crsKey === 'custom') {
    var baseLat = parseFloat(document.getElementById('datumLat').value) || 3.139003;
    var baseLng = parseFloat(document.getElementById('datumLng').value) || 101.686855;
    origin = { lat: baseLat, lng: baseLng, e0: 0, n0: 0, a: 6378137.0, f: 1/298.257222101 };
  }
  return origin;
}

function getWGS84Coords(easting, northing) {
  var origin = getCrsOrigin();
  var a = origin.a;
  var f = origin.f;

  var e2 = 2 * f - f * f; 
  var lat0 = origin.lat * (Math.PI / 180);
  var lng0 = origin.lng * (Math.PI / 180);

  function meridianDistance(phi) {
    return a * ((1 - e2/4 - 3*e2*e2/64 - 5*e2*e2*e2/256) * phi -
                (3*e2/8 + 3*e2*e2/32 + 45*e2*e2*e2/1024) * Math.sin(2*phi) +
                (15*e2*e2/256 + 45*e2*e2*e2/1024) * Math.sin(4*phi) -
                (35*e2*e2/3072) * Math.sin(6*phi));
  }

  var dx = easting - origin.e0;
  var dy = northing - origin.n0;

  var M0 = meridianDistance(lat0);
  var M1 = M0 + dy;

  var phi1 = lat0;
  for (var i = 0; i < 7; i++) {
    phi1 = phi1 + (M1 - meridianDistance(phi1)) / a;
  }

  var sinPhi1 = Math.sin(phi1);
  var cosPhi1 = Math.cos(phi1);
  var tanPhi1 = Math.tan(phi1);

  var N1 = a / Math.sqrt(1 - e2 * sinPhi1 * sinPhi1);
  var R1 = a * (1 - e2) / Math.pow(1 - e2 * sinPhi1 * sinPhi1, 1.5);
  var T1 = tanPhi1 * tanPhi1;
  var D = dx / N1;

  var lat = phi1 - (tanPhi1 * N1 / R1) * ((D * D / 2) - (1 + 3 * T1) * (Math.pow(D, 4) / 24));
  var lng = lng0 + (D - T1 * (Math.pow(D, 3) / 3) + (1 + 3 * T1) * T1 * (Math.pow(D, 5) / 15)) / cosPhi1;

  return { lat: lat * (180 / Math.PI), lng: lng * (180 / Math.PI) };
}

function wgs84ToCassini(lat, lng) {
  var origin = getCrsOrigin();
  var a = origin.a;
  var f = origin.f;

  var e2 = 2 * f - f * f;
  var latRad = lat * (Math.PI / 180);
  var lngRad = lng * (Math.PI / 180);
  var lat0 = origin.lat * (Math.PI / 180);
  var lng0 = origin.lng * (Math.PI / 180);

  function meridianDistance(phi) {
    return a * ((1 - e2/4 - 3*e2*e2/64 - 5*e2*e2*e2/256) * phi -
                (3*e2/8 + 3*e2*e2/32 + 45*e2*e2*e2/1024) * Math.sin(2*phi) +
                (15*e2*e2/256 + 45*e2*e2*e2/1024) * Math.sin(4*phi) -
                (35*e2*e2/3072) * Math.sin(6*phi));
  }

  var M = meridianDistance(latRad);
  var M0 = meridianDistance(lat0);

  var sinLat = Math.sin(latRad);
  var cosLat = Math.cos(latRad);
  var tanLat = Math.tan(latRad);

  var N = a / Math.sqrt(1 - e2 * sinLat * sinLat);
  var T = tanLat * tanLat;
  var A = (lngRad - lng0) * cosLat;
  var C = (e2 / (1 - e2)) * (cosLat * cosLat);

  var easting = origin.e0 + N * (A - T * Math.pow(A, 3) / 6 - (8 - T + 8 * C) * T * Math.pow(A, 5) / 120);
  var northing = origin.n0 + M - M0 + N * tanLat * (Math.pow(A, 2) / 2 + (5 - T + 6 * C) * Math.pow(A, 4) / 24);

  return { e: easting, n: northing };
}

function setupKeyboardListeners() {
  window.addEventListener('keydown', function(e) {
    if (e.key === 'Escape') {
      clearSelections();
      if (isMeasureMode) toggleMeasureTool();
      if (isAreaMode) toggleAreaTool();
      if (pickTargetField) togglePickMode(pickTargetField);
      if (isLotCreationMode) {
        isLotCreationMode = false;
        document.getElementById('pickBanner').style.display = 'none';
        canvas.classList.remove('pick-cursor');
      }
    } else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') {
      if (e.shiftKey) { redo(); } else { undo(); }
    } else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'y') {
      redo();
    }
  });
}

function pushState() {
  undoStack.push({
    points: JSON.parse(JSON.stringify(points)),
    legs: JSON.parse(JSON.stringify(legs)),
    lotRecords: JSON.parse(JSON.stringify(lotRecords)),
    datumPoints: JSON.parse(JSON.stringify(datumPoints))
  });
  redoStack = [];
  updateUndoRedoUI();
}

function undo() {
  if (undoStack.length === 0) return;

  redoStack.push({
    points: JSON.parse(JSON.stringify(points)),
    legs: JSON.parse(JSON.stringify(legs)),
    lotRecords: JSON.parse(JSON.stringify(lotRecords)),
    datumPoints: JSON.parse(JSON.stringify(datumPoints))
  });

  var previousState = undoStack.pop();
  points = previousState.points;
  legs = previousState.legs;
  lotRecords = previousState.lotRecords || [];
  datumPoints = previousState.datumPoints || [];

  relinkLegPointers();
  updateLineLogDropdowns();
  updateTable();
  updateStnTable();
  updateLotTable();
  updateUndoRedoUI();
  drawCAD();
  showToast("Undo applied.", "info");
}

function redo() {
  if (redoStack.length === 0) return;

  undoStack.push({
    points: JSON.parse(JSON.stringify(points)),
    legs: JSON.parse(JSON.stringify(legs)),
    lotRecords: JSON.parse(JSON.stringify(lotRecords)),
    datumPoints: JSON.parse(JSON.stringify(datumPoints))
  });

  var nextState = redoStack.pop();
  points = nextState.points;
  legs = nextState.legs;
  lotRecords = nextState.lotRecords || [];
  datumPoints = nextState.datumPoints || [];

  relinkLegPointers();
  updateLineLogDropdowns();
  updateTable();
  updateStnTable();
  updateLotTable();
  updateUndoRedoUI();
  drawCAD();
  showToast("Redo applied.", "info");
}

function relinkLegPointers() {
  legs.forEach(function(leg) {
    leg.p1 = points.find(p => p.id === leg.from);
    leg.p2 = points.find(p => p.id === leg.to);
  });
}

function recomputeTraverseChain() {
  if (legs.length === 0) return;

  legs.forEach(function(leg) {
    var startPt = points.find(p => p.id === leg.from);
    if (!startPt) return;

    var decDeg = leg.deg + (leg.min / 60) + (leg.sec / 3600);
    var rad = decDeg * (Math.PI / 180);

    var dE = leg.dist * Math.sin(rad);
    var dN = leg.dist * Math.cos(rad);

    var targetPt = points.find(p => p.id === leg.to);
    if (!targetPt) {
      targetPt = { id: leg.to, e: startPt.e + dE, n: startPt.n + dN };
      points.push(targetPt);
    } else {
      if (!datumPoints.includes(targetPt.id)) {
        targetPt.e = startPt.e + dE;
        targetPt.n = startPt.n + dN;
      }
    }

    leg.p1 = startPt;
    leg.p2 = targetPt;
  });

  updateTable();
  drawCAD();
}

function updateUndoRedoUI() {
  var canUndo = undoStack.length > 0;
  var canRedo = redoStack.length > 0;

  document.getElementById('undoBtnTop').disabled = !canUndo;
  document.getElementById('redoBtnTop').disabled = !canRedo;
}

function zoomIn() { zoomFactor *= 1.25; drawCAD(); }
function zoomOut() { zoomFactor *= 0.8; drawCAD(); }

function centerOnWismaPersekutuan() {
  var centerE = 21528.250;
  var centerN = -63868.520;
  var defaultSpan = 350;

  var padding = 120;
  var baseScale = Math.min((canvas.width - padding * 2) / defaultSpan, (canvas.height - padding * 2) / defaultSpan);

  zoomFactor = 1;
  panX = (canvas.width / 2) - padding;
  panY = (canvas.height / 2) - (canvas.height - padding);

  drawCAD(centerE, centerN, defaultSpan);
}

function zoomExtents() {
  zoomFactor = 1;
  if (points.length === 0) {
    centerOnWismaPersekutuan();
    return;
  }

  var minE = Math.min(...points.map(p => p.e));
  var maxE = Math.max(...points.map(p => p.e));
  var minN = Math.min(...points.map(p => p.n));
  var maxN = Math.max(...points.map(p => p.n));

  var rangeE = (maxE - minE) || 50;
  var rangeN = (maxN - minN) || 50;

  var padding = 120;
  var baseScale = Math.min((canvas.width - padding * 2) / rangeE, (canvas.height - padding * 2) / rangeN);

  var rawMinX = padding;
  var rawMaxX = padding + rangeE * baseScale;
  var rawMinY = canvas.height - (padding + rangeN * baseScale);
  var rawMaxY = canvas.height - padding;

  panX = (canvas.width / 2) - ((rawMinX + rawMaxX) / 2);
  panY = (canvas.height / 2) - ((rawMinY + rawMaxY) / 2);

  drawCAD();
}

function reverseBearing() {
  var deg = Number(document.getElementById('deg').value) || 0;
  var min = Number(document.getElementById('min').value) || 0;
  var sec = Number(document.getElementById('sec').value) || 0;

  var totalDecimal = deg + (min / 60) + (sec / 3600);
  totalDecimal = (totalDecimal < 180) ? (totalDecimal + 180) : (totalDecimal - 180);

  var newDeg = Math.floor(totalDecimal);
  var remainderMin = (totalDecimal - newDeg) * 60;
  var newMin = Math.floor(remainderMin);
  var newSec = Math.round((remainderMin - newMin) * 60);

  if (newSec === 60) { newSec = 0; newMin += 1; }
  if (newMin === 60) { newMin = 0; newDeg = (newDeg + 1) % 360; }

  document.getElementById('deg').value = newDeg;
  document.getElementById('min').value = newMin;
  document.getElementById('sec').value = newSec;
}

function updateUnitPreview() {
  var rawDist = Number(document.getElementById('dist').value);
  var unit = document.getElementById('unitSelect').value;
  var hint = document.getElementById('unitHint');

  if (unit === 'lk' && !isNaN(rawDist) && rawDist > 0) {
    hint.innerText = `= ${(rawDist * LINK_TO_METER).toFixed(3)} m (${rawDist} lk × 0.201168)`;
  } else {
    hint.innerText = '';
  }
}

function getNextStationId(currentId) {
  if (!currentId) return '';
  var match = currentId.match(/^(.*?)(\d+)$/);
  if (match) {
    var prefix = match[1];
    var numStr = match[2];
    var nextNum = (parseInt(numStr, 10) + 1).toString().padStart(numStr.length, '0');
    return prefix + nextNum;
  }
  return '';
}

function addLeg() {
  var fromStnId = document.getElementById('fromStn').value.trim();
  var toStnId = document.getElementById('toStn').value.trim();
  
  var deg = Number(document.getElementById('deg').value) || 0;
  var min = Number(document.getElementById('min').value) || 0;
  var sec = Number(document.getElementById('sec').value) || 0;
  
  var rawDist = Number(document.getElementById('dist').value);
  var unit = document.getElementById('unitSelect').value;

  if (!fromStnId || !toStnId) {
    showToast("Please enter valid From STN and To STN IDs.", "warning");
    return;
  }

  if (fromStnId.toLowerCase() === toStnId.toLowerCase()) {
    showToast("Error: 'From STN' and 'To STN' cannot be identical (" + fromStnId + ")!", "warning");
    return;
  }

  if (isNaN(rawDist) || rawDist <= 0) {
    showToast("Please enter a valid positive distance.", "warning");
    return;
  }

  var distMeter = (unit === 'lk') ? (rawDist * LINK_TO_METER) : rawDist;

  var startPoint = points.find(p => p.id === fromStnId);
  if (!startPoint) {
    showToast("Station '" + fromStnId + "' does not exist in drawing! Please configure a Fix Point first.", "warning");
    return;
  }

  var decDeg = deg + (min / 60) + (sec / 3600);
  var rad = decDeg * (Math.PI / 180);

  var dE = distMeter * Math.sin(rad);
  var dN = distMeter * Math.cos(rad);

  var calcE = startPoint.e + dE;
  var calcN = startPoint.n + dN;

  var existingTarget = points.find(p => p.id === toStnId);

  if (existingTarget) {
    var misclosureDist = Math.hypot(calcE - existingTarget.e, calcN - existingTarget.n);

    if (misclosureDist > 0.05) { 
      pendingLegData = {
        fromStnId: fromStnId,
        toStnId: toStnId,
        deg: deg, min: min, sec: sec,
        distMeter: distMeter, rawDist: rawDist, unit: unit,
        calcE: calcE, calcN: calcN,
        startPoint: startPoint,
        misclosureDist: misclosureDist
      };

      document.getElementById('closureWarningBody').innerHTML = 
        `Target station <b>${toStnId}</b> exists, but your inputted bearing/distance lands <b>${misclosureDist.toFixed(3)}m</b> away (outside 0.05m tolerance).<br><br>` +
        `If you proceed, the line will be drawn to your calculated location and create a duplicate station node on canvas.`;

      document.getElementById('closureModal').style.display = 'flex';
      return;
    } else {
      commitLegAddition(fromStnId, toStnId, deg, min, sec, distMeter, rawDist, unit, startPoint, existingTarget);
      return;
    }
  }

  var newTarget = { id: toStnId, e: calcE, n: calcN };
  points.push(newTarget);
  commitLegAddition(fromStnId, toStnId, deg, min, sec, distMeter, rawDist, unit, startPoint, newTarget);
}

function confirmProceedDuplicate() {
  if (!pendingLegData) return;

  var d = pendingLegData;
  var duplicateTarget = { id: d.toStnId, e: d.calcE, n: d.calcN };
  points.push(duplicateTarget);

  commitLegAddition(d.fromStnId, d.toStnId, d.deg, d.min, d.sec, d.distMeter, d.rawDist, d.unit, d.startPoint, duplicateTarget);
  closeClosureModal();
}

function closeClosureModal() {
  pendingLegData = null;
  document.getElementById('closureModal').style.display = 'none';
}

function commitLegAddition(fromStnId, toStnId, deg, min, sec, distMeter, rawDist, unit, startPoint, targetPoint) {
  pushState();
  var pad = n => String(n).padStart(2, '0');

  legs.push({
    from: fromStnId,
    to: toStnId,
    deg: deg,
    min: min,
    sec: sec,
    dmsFormatted: deg + "-" + pad(min) + "-" + pad(sec),
    dist: distMeter,
    rawDist: rawDist,
    rawUnit: unit,
    p1: startPoint,
    p2: targetPoint
  });

  document.getElementById('fromStn').value = toStnId;
  document.getElementById('toStn').value = getNextStationId(toStnId);

  updateLineLogDropdowns();
  updateTable();
  updateStnTable();
  updateUndoRedoUI();
  drawCAD();
}

function editLeg(index, e) {
  if (e) e.stopPropagation();
  var leg = legs[index];

  document.getElementById('editLegIndex').value = index;
  document.getElementById('editFromStn').value = leg.from;
  document.getElementById('editToStn').value = leg.to;
  document.getElementById('editDeg').value = leg.deg;
  document.getElementById('editMin').value = leg.min;
  document.getElementById('editSec').value = leg.sec;
  document.getElementById('editDist').value = leg.dist.toFixed(3);

  document.getElementById('editModal').style.display = 'flex';
}

function closeEditModal() {
  document.getElementById('editModal').style.display = 'none';
}

function saveLegEdit() {
  var index = parseInt(document.getElementById('editLegIndex').value, 10);
  var fromId = document.getElementById('editFromStn').value.trim();
  var toId = document.getElementById('editToStn').value.trim();
  var deg = Number(document.getElementById('editDeg').value) || 0;
  var min = Number(document.getElementById('editMin').value) || 0;
  var sec = Number(document.getElementById('editSec').value) || 0;
  var dist = parseFloat(document.getElementById('editDist').value);

  if (!fromId || !toId || isNaN(dist) || dist <= 0) {
    showToast("Please enter valid From STN, To STN, Bearing, and Distance.", "warning");
    return;
  }

  pushState();

  var pad = n => String(n).padStart(2, '0');
  var leg = legs[index];

  leg.from = fromId;
  leg.to = toId;
  leg.deg = deg;
  leg.min = min;
  leg.sec = sec;
  leg.dmsFormatted = deg + "-" + pad(min) + "-" + pad(sec);
  leg.dist = dist;
  leg.rawDist = dist;
  leg.rawUnit = 'm';

  closeEditModal();
  recomputeTraverseChain();
  updateLineLogDropdowns();
  updateStnTable();
  showToast("Line record updated.", "success");
}

function editLot(lotIdx, e) {
  if (e) e.stopPropagation();
  var lot = lotRecords[lotIdx];

  document.getElementById('editLotIndex').value = lotIdx;
  document.getElementById('editLotPa').value = lot.pa;
  document.getElementById('editLotUpi').value = lot.upi;
  document.getElementById('editLotNodesStr').value = lot.nodes.join(',');

  document.getElementById('editLotModal').style.display = 'flex';
}

function closeEditLotModal() {
  document.getElementById('editLotModal').style.display = 'none';
}

function saveLotEdit() {
  var lotIdx = parseInt(document.getElementById('editLotIndex').value, 10);
  var pa = document.getElementById('editLotPa').value.trim();
  var upi = document.getElementById('editLotUpi').value.trim();
  var nodesStr = document.getElementById('editLotNodesStr').value.trim();

  if (!pa || !upi || !nodesStr) {
    showToast("Please enter valid PA, UPI, and Node Sequence.", "warning");
    return;
  }

  var nodesArr = nodesStr.split(',').map(s => s.trim()).filter(s => s.length > 0);
  if (nodesArr.length < 3) {
    showToast("A valid lot sequence must contain at least 3 nodes.", "warning");
    return;
  }

  pushState();

  var lotDisplayNo = extractLotNoFromUpi(upi);

  var lot = lotRecords[lotIdx];
  lot.pa = pa;
  lot.upi = upi;
  lot.lotNo = lotDisplayNo;
  lot.nodes = nodesArr;

  closeEditLotModal();
  updateLotTable();
  drawCAD();
  showToast("Lot record updated.", "success");
}

function deleteLeg(index, e) {
  if (e) e.stopPropagation();
  var legToDelete = legs[index];

  pushState();
  legs.splice(index, 1);
  if (selectedLegIndex === index) selectedLegIndex = null;
  updateLineLogDropdowns();
  updateTable();
  updateStnTable();
  updateUndoRedoUI();
  drawCAD();
  showToast(`Deleted line ${legToDelete.from} ➔ ${legToDelete.to}`, "info");
}

function deleteLot(lotIdx) {
  var lot = lotRecords[lotIdx];
  pushState();
  lotRecords.splice(lotIdx, 1);
  selectedLotIndex = null;
  updateLotTable();
  drawCAD();
  showToast(`Deleted Lot record [${lot.pa} | Lot ${lot.lotNo}]`, "info");
}

function openExportModal() {
  if (legs.length === 0) {
    showToast("No line records available to export!", "warning");
    return;
  }
  document.getElementById('exportModal').style.display = 'flex';
}

function closeExportModal() {
  document.getElementById('exportModal').style.display = 'none';
}

function executeExport() {
  var format = document.getElementById('exportFormat').value;

  if (format === 'txt') {
    downloadTxtFile();
  } else if (format === 'dxf') {
    downloadDxfFile();
  } else if (format === 'kml') {
    downloadKmlFile();
  }
  closeExportModal();
}

function downloadTxtFile() {
  var bWeight = document.getElementById('bearingWeight').value.trim() || '15';
  var dWeight = document.getElementById('distanceWeight').value.trim() || '0.01';

  var lines = [];
  legs.forEach(function(leg) {
    lines.push(`B ${leg.from}-${leg.to} ${leg.dmsFormatted} ${bWeight}`);
    lines.push(`D ${leg.from}-${leg.to} ${leg.dist.toFixed(3)} ${dWeight}`);
  });

  triggerFileDownload(lines.join('\n'), 'KDE_NEXT_LEVEL_Export.txt', 'text/plain');
}

function exportLotStnTxt() {
  if (lotRecords.length === 0) {
    showToast("No Lot Stn records available to export! Click '+ Create New Lot Stn' first.", "warning");
    return;
  }

  var lines = ["PA\tUPI\tOrder\tNode"];
  lotRecords.forEach(function(lot) {
    lot.nodes.forEach(function(stnId, idx) {
      lines.push(`${lot.pa}\t${lot.upi}\t${idx + 1}\t${stnId}`);
    });
  });

  triggerFileDownload(lines.join('\n'), 'KDE_Lot_Stn_Export.txt', 'text/plain');
}

function downloadDxfFile() {
  var dxf = [];
  dxf.push("0\nSECTION\n2\nHEADER\n0\nENDSEC");
  dxf.push("0\nSECTION\n2\nENTITIES");

  legs.forEach(function(leg) {
    dxf.push(`0\nLINE\n8\nBOUNDARY_LINES\n10\n${leg.p1.e}\n20\n${leg.p1.n}\n30\n0.0\n11\n${leg.p2.e}\n21\n${leg.p2.n}\n31\n0.0`);
  });

  points.forEach(function(pt) {
    dxf.push(`0\nPOINT\n8\nSTATION_NODES\n10\n${pt.e}\n20\n${pt.n}\n30\n0.0`);
    dxf.push(`0\nTEXT\n8\nSTATION_TEXT\n10\n${pt.e + 1}\n20\n${pt.n + 1}\n30\n0.0\n40\n1.5\n1\n${pt.id}`);
  });

  lotRecords.forEach(function(lot) {
    var lotPts = [];
    lot.nodes.forEach(stnId => {
      var pt = points.find(p => p.id === stnId);
      if (pt) lotPts.push(pt);
    });

    if (lotPts.length >= 3) {
      var geom = computePolygonAreaAndPerimeter(lotPts);
      var cE = lotPts.reduce((acc, p) => acc + p.e, 0) / lotPts.length;
      var cN = lotPts.reduce((acc, p) => acc + p.n, 0) / lotPts.length;

      dxf.push(`0\nTEXT\n8\nLOT_IDENTIFIER\n10\n${cE}\n20\n${cN + 2}\n30\n0.0\n40\n2.0\n1\nLot ${lot.lotNo}`);
      dxf.push(`0\nTEXT\n8\nLOT_AREA_TEXT\n10\n${cE}\n20\n${cN - 2}\n30\n0.0\n40\n1.4\n1\n${geom.areaSqM.toFixed(1)} sq.m`);
    }
  });

  dxf.push("0\nENDSEC\n0\nEOF");
  triggerFileDownload(dxf.join('\n'), 'KDE_Traverse_Plot.dxf', 'image/vnd.dxf');
}

function downloadKmlFile() {
  if (points.length === 0) return;

  var placemarks = [];

  if (lotRecords.length > 0) {
    lotRecords.forEach(function(lot) {
      var lotCoords = [];
      var lotPts = [];
      lot.nodes.forEach(function(stnId) {
        var p = points.find(pt => pt.id === stnId);
        if (p) {
          lotPts.push(p);
          var gps = getWGS84Coords(p.e, p.n);
          lotCoords.push(`${gps.lng.toFixed(7)},${gps.lat.toFixed(7)},0`);
        }
      });

      var geom = computePolygonAreaAndPerimeter(lotPts);

      if (lotCoords.length >= 3) {
        if (lotCoords[0] !== lotCoords[lotCoords.length - 1]) {
          lotCoords.push(lotCoords[0]);
        }

        placemarks.push(`
    <Placemark>
      <name>Lot ${lot.lotNo} (${lot.pa})</name>
      <description><![CDATA[
        <b>PA No:</b> ${lot.pa}<br>
        <b>UPI:</b> ${lot.upi}<br>
        <b>Area:</b> ${geom.areaSqM.toFixed(2)} m² (${geom.areaAc.toFixed(3)} ac / ${geom.areaHa.toFixed(3)} ha)<br>
        <b>Perimeter:</b> ${geom.perimeterM.toFixed(2)} m
      ]]></description>
      <styleUrl>#lotStyle</styleUrl>
      <Polygon>
        <tessellate>1</tessellate>
        <outerBoundaryIs>
          <LinearRing><coordinates>${lotCoords.join(' ')}</coordinates></LinearRing>
        </outerBoundaryIs>
      </Polygon>
    </Placemark>`);
      }
    });
  }

  if (legs.length > 0) {
    legs.forEach(function(leg) {
      var gps1 = getWGS84Coords(leg.p1.e, leg.p1.n);
      var gps2 = getWGS84Coords(leg.p2.e, leg.p2.n);
      var pairCoords = `${gps1.lng.toFixed(7)},${gps1.lat.toFixed(7)},0 ${gps2.lng.toFixed(7)},${gps2.lat.toFixed(7)},0`;

      placemarks.push(`
    <Placemark>
      <name>${leg.from} - ${leg.to}</name>
      <styleUrl>#lineStyle</styleUrl>
      <LineString>
        <tessellate>1</tessellate>
        <coordinates>${pairCoords}</coordinates>
      </LineString>
    </Placemark>`);
    });
  }

  points.forEach(function(p) {
    var gps = getWGS84Coords(p.e, p.n);
    var isDatum = datumPoints.includes(p.id);
    var labelTitle = isDatum ? `FIX ${p.id}` : `STN ${p.id}`;

    placemarks.push(`
    <Placemark>
      <name>${labelTitle}</name>
      <styleUrl>${isDatum ? '#datumPointStyle' : '#stnPointStyle'}</styleUrl>
      <Point>
        <coordinates>${gps.lng.toFixed(7)},${gps.lat.toFixed(7)},0</coordinates>
      </Point>
    </Placemark>`);
  });

  var kml = `<?xml version="1.0" encoding="UTF-8"?>
<kml xmlns="http://www.opengis.net/kml/2.2">
  <Document>
    <name>KDE Cadastral Survey Export</name>

    <Style id="lotStyle">
      <LineStyle><color>ff00f2ff</color><width>2.5</width></LineStyle>
      <PolyStyle><color>4000ffea</color></PolyStyle>
    </Style>

    <Style id="lineStyle">
      <LineStyle><color>ff00f2ff</color><width>2.5</width></LineStyle>
    </Style>

    <Style id="stnPointStyle">
      <IconStyle>
        <scale>0.8</scale>
        <Icon><href>http://maps.google.com/mapfiles/kml/paddle/red-circle.png</href></Icon>
      </IconStyle>
      <LabelStyle><scale>0.85</scale></LabelStyle>
    </Style>

    <Style id="datumPointStyle">
      <IconStyle>
        <scale>1.0</scale>
        <Icon><href>http://maps.google.com/mapfiles/kml/paddle/ylw-blank.png</href></Icon>
      </IconStyle>
      <LabelStyle><scale>0.9</scale></LabelStyle>
    </Style>

    ${placemarks.join('')}
  </Document>
</kml>`;

  triggerFileDownload(kml, 'KDE_Cadastral_Survey.kml', 'application/vnd.google-earth.kml+xml');
}

function triggerFileDownload(content, filename, contentType) {
  var blob = new Blob([content], { type: contentType });
  var link = document.createElement('a');
  link.href = URL.createObjectURL(blob);
  link.download = filename;
  link.click();
  showToast(`Downloaded ${filename}`, "success");
}

function updateLineLogDropdowns() {
  var fromSelect = document.getElementById('filterFromStn');
  var toSelect = document.getElementById('filterToStn');
  if (!fromSelect || !toSelect) return;

  var curFrom = fromSelect.value;
  var curTo = toSelect.value;

  var uniqueFrom = [...new Set(legs.map(l => l.from))].sort();
  var uniqueTo = [...new Set(legs.map(l => l.to))].sort();

  var fromHtml = '<option value="">All From</option>';
  uniqueFrom.forEach(id => {
    fromHtml += `<option value="${id}" ${id === curFrom ? 'selected' : ''}>${id}</option>`;
  });
  fromSelect.innerHTML = fromHtml;

  var toHtml = '<option value="">All To</option>';
  uniqueTo.forEach(id => {
    toHtml += `<option value="${id}" ${id === curTo ? 'selected' : ''}>${id}</option>`;
  });
  toSelect.innerHTML = toHtml;
}

function updateTable() {
  var tbody = document.querySelector('#traverseTable tbody');
  if (!tbody) return;
  tbody.innerHTML = '';

  var fromFilter = document.getElementById('filterFromStn') ? document.getElementById('filterFromStn').value : '';
  var toFilter = document.getElementById('filterToStn') ? document.getElementById('filterToStn').value : '';

  var badge = document.getElementById('lineCountBadge');
  if (badge) badge.innerText = legs.length;

  legs.forEach((leg, idx) => {
    var matchesFrom = !fromFilter || leg.from === fromFilter;
    var matchesTo = !toFilter || leg.to === toFilter;

    if (matchesFrom && matchesTo) {
      var isSelected = (idx === selectedLegIndex || selectedLegIndices.includes(idx));
      tbody.innerHTML += `<tr id="legRow_${idx}" class="${isSelected ? 'selected-row' : ''}" onclick="selectLegRecord(${idx}, false)">
        <td>${leg.from}</td>
        <td>${leg.to}</td>
        <td>${leg.dmsFormatted}</td>
        <td>${leg.dist.toFixed(3)}</td>
        <td>
          <button class="tbl-btn" onclick="editLeg(${idx}, event)" title="Edit Record">✏️</button>
          <button class="tbl-btn" onclick="deleteLeg(${idx}, event)" title="Delete Record">🗑️</button>
        </td>
      </tr>`;
    }
  });
}

function updateStnTable() {
  var tbody = document.querySelector('#stnTable tbody');
  if (!tbody) return;
  tbody.innerHTML = '';

  var filter = (document.getElementById('stnSearchFilter') ? document.getElementById('stnSearchFilter').value.trim().toLowerCase() : '');
  var countBadge = document.getElementById('stnCountBadge');
  if (countBadge) countBadge.innerText = points.length;

  points.forEach((pt) => {
    if (!filter || pt.id.toLowerCase().includes(filter)) {
      var isFix = datumPoints.includes(pt.id);
      tbody.innerHTML += `<tr>
        <td style="font-weight: bold; color: ${isFix ? '#ffea00' : '#ffffff'};">${pt.id}</td>
        <td><span style="font-size: 10px; font-weight: 700; color: ${isFix ? '#ffea00' : '#00f2ff'};">${isFix ? 'FIX 🔺' : 'STN ⭕'}</span></td>
        <td>${pt.e.toFixed(3)}</td>
        <td>${pt.n.toFixed(3)}</td>
        <td>
          <button class="tbl-btn" onclick="openDatumModal('${pt.id}')" title="Configure Coordinates / Fix">✏️</button>
          <button class="tbl-btn" onclick="promptDeleteStation('${pt.id}')" title="Delete Station">🗑️</button>
        </td>
      </tr>`;
    }
  });
}

function updateLotTable() {
  var tbody = document.querySelector('#lotTable tbody');
  if (!tbody) return;
  tbody.innerHTML = '';
  
  var totalArea = 0;

  lotRecords.forEach((lot, lotIdx) => {
    var lotPts = [];
    lot.nodes.forEach(stnId => {
      var pt = points.find(p => p.id === stnId);
      if (pt) lotPts.push(pt);
    });

    var geom = computePolygonAreaAndPerimeter(lotPts);
    totalArea += geom.areaSqM;

    lot.nodes.forEach((stnId, orderIdx) => {
      var isSelected = (lotIdx === selectedLotIndex);
      tbody.innerHTML += `<tr id="lotRow_${lotIdx}_${orderIdx}" data-lot-idx="${lotIdx}" class="${isSelected ? 'selected-row' : ''}" onclick="selectLotRecord(${lotIdx}, false)">
        <td>${lot.pa}</td>
        <td style="font-family: monospace;">${orderIdx === 0 ? `Lot ${lot.lotNo}` : lot.upi}</td>
        <td>${orderIdx === 0 ? `${geom.areaSqM.toFixed(1)} m²` : '-'}</td>
        <td>${stnId}</td>
        <td>
          ${orderIdx === 0 ? `
            <button class="tbl-btn" onclick="editLot(${lotIdx}, event)" title="Edit Lot Record">✏️</button>
            <button class="tbl-btn" onclick="deleteLot(${lotIdx})" title="Delete Lot">🗑️</button>
          ` : ''}
        </td>
      </tr>`;
    });
  });

  var areaBadge = document.getElementById('totalLotAreaBadge');
  if (areaBadge) areaBadge.innerText = `Total: ${totalArea.toFixed(1)} m² (${(totalArea / 10000).toFixed(3)} ha)`;
}

function drawCAD(overrideCenterE, overrideCenterN, overrideSpan) {
  ctx.fillStyle = "#090a0e";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  ctx.font = 'bold 12px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif';
  ctx.fillStyle = 'rgba(255, 255, 255, 0.25)';
  ctx.textAlign = 'right';
  ctx.fillText('Copyright © CPDG Johor', canvas.width - 20, canvas.height - 18);
  ctx.textAlign = 'left';

  var minE, maxE, minN, maxN, rangeE, rangeN;

  // If no points are entered, use Wisma Persekutuan JB default camera viewport
  if (points.length === 0) {
    var cE = overrideCenterE || 21528.250;
    var cN = overrideCenterN || -63868.520;
    var span = overrideSpan || 350;
    minE = cE - span / 2;
    maxE = cE + span / 2;
    minN = cN - span / 2;
    maxN = cN + span / 2;
    rangeE = span;
    rangeN = span;
  } else {
    minE = Math.min(...points.map(p => p.e));
    maxE = Math.max(...points.map(p => p.e));
    minN = Math.min(...points.map(p => p.n));
    maxN = Math.max(...points.map(p => p.n));
    rangeE = (maxE - minE) || 50;
    rangeN = (maxN - minN) || 50;
  }

  var padding = 120;
  var baseScale = Math.min((canvas.width - padding * 2) / rangeE, (canvas.height - padding * 2) / rangeN);

  // 1. Render Basemap Tile Layer
  renderBasemapTiles(minE, minN, baseScale, padding);

  // If there are no points plotted yet, stop here to avoid drawing null geometries
  if (points.length === 0) return;

  var showStnLabels = document.getElementById('showStnLabelsToggle') ? document.getElementById('showStnLabelsToggle').checked : true;
  var showLineData = document.getElementById('showLineDataToggle') ? document.getElementById('showLineDataToggle').checked : true;
  var showLotArea = document.getElementById('showLotAreaToggle') ? document.getElementById('showLotAreaToggle').checked : true;

  // 2. Draw Lot Polygons & Labels
  lotRecords.forEach((lot, lIdx) => {
    var lotPts = [];
    lot.nodes.forEach(stnId => {
      var pt = points.find(p => p.id === stnId);
      if (pt) lotPts.push(pt);
    });

    if (lotPts.length >= 3) {
      ctx.beginPath();
      var startScr = toScreen(lotPts[0].e, lotPts[0].n, padding, baseScale, minE, minN);
      ctx.moveTo(startScr.x, startScr.y);

      var sumX = startScr.x;
      var sumY = startScr.y;

      for (var k = 1; k < lotPts.length; k++) {
        var scr = toScreen(lotPts[k].e, lotPts[k].n, padding, baseScale, minE, minN);
        ctx.lineTo(scr.x, scr.y);
        sumX += scr.x;
        sumY += scr.y;
      }

      ctx.closePath();
      ctx.fillStyle = (lIdx === selectedLotIndex) ? 'rgba(255, 234, 0, 0.3)' : 'rgba(0, 242, 255, 0.14)';
      ctx.fill();
      ctx.strokeStyle = (lIdx === selectedLotIndex) ? '#ffea00' : '#00f2ff';
      ctx.lineWidth = (lIdx === selectedLotIndex) ? 3 : 2;
      ctx.stroke();

      var centroidX = sumX / lotPts.length;
      var centroidY = sumY / lotPts.length;
      var geom = computePolygonAreaAndPerimeter(lotPts);

      var labelStr = `Lot ${lot.lotNo}`;
      ctx.font = 'bold 15px sans-serif';
      ctx.strokeStyle = '#000000';
      ctx.lineWidth = 4;
      ctx.strokeText(labelStr, centroidX - 16, centroidY - 4);
      ctx.fillStyle = '#ffea00';
      ctx.fillText(labelStr, centroidX - 16, centroidY - 4);

      if (showLotArea) {
        var areaLabel = `${geom.areaSqM.toFixed(1)} m² (${geom.areaAc.toFixed(2)} ac)`;
        ctx.font = 'bold 11px monospace';
        ctx.strokeStyle = '#000000';
        ctx.lineWidth = 3;
        ctx.strokeText(areaLabel, centroidX - 16, centroidY + 12);
        ctx.fillStyle = '#25d366';
        ctx.fillText(areaLabel, centroidX - 16, centroidY + 12);
      }

      if (lIdx === selectedLotIndex) {
        lot.nodes.forEach((stnId, orderIdx) => {
          var nodePt = points.find(p => p.id === stnId);
          if (nodePt) {
            var nScr = toScreen(nodePt.e, nodePt.n, padding, baseScale, minE, minN);
            ctx.beginPath();
            ctx.arc(nScr.x - 12, nScr.y - 12, 10, 0, 2 * Math.PI);
            ctx.fillStyle = '#ffea00';
            ctx.fill();
            ctx.strokeStyle = '#000000';
            ctx.lineWidth = 1.5;
            ctx.stroke();

            ctx.font = 'bold 11px sans-serif';
            ctx.fillStyle = '#000000';
            ctx.textAlign = 'center';
            ctx.fillText(orderIdx + 1, nScr.x - 12, nScr.y - 8);
            ctx.textAlign = 'left';
          }
        });
      }
    }
  });

  // 3. Render In-Progress Active Lot Creation or Measure Area Polygon
  var activePolygonNodes = isLotCreationMode ? activeLotNodes : (isAreaMode ? areaPoints.map(p => p.id) : []);
  if (activePolygonNodes.length >= 1) {
    ctx.beginPath();
    var p0 = points.find(p => p.id === activePolygonNodes[0]);
    if (p0) {
      var scr0 = toScreen(p0.e, p0.n, padding, baseScale, minE, minN);
      ctx.moveTo(scr0.x, scr0.y);

      for (var m = 1; m < activePolygonNodes.length; m++) {
        var pm = points.find(p => p.id === activePolygonNodes[m]);
        if (pm) {
          var scrm = toScreen(pm.e, pm.n, padding, baseScale, minE, minN);
          ctx.lineTo(scrm.x, scrm.y);
        }
      }

      ctx.strokeStyle = isAreaMode ? '#25d366' : '#ffea00';
      ctx.lineWidth = 2;
      ctx.setLineDash([5, 3]);
      ctx.stroke();
      ctx.setLineDash([]);
    }

    activePolygonNodes.forEach((stnId, orderIdx) => {
      var nodePt = points.find(p => p.id === stnId);
      if (nodePt) {
        var nScr = toScreen(nodePt.e, nodePt.n, padding, baseScale, minE, minN);
        ctx.beginPath();
        ctx.arc(nScr.x - 12, nScr.y - 12, 10, 0, 2 * Math.PI);
        ctx.fillStyle = isAreaMode ? '#25d366' : '#ffea00';
        ctx.fill();
        ctx.strokeStyle = '#000000';
        ctx.lineWidth = 1.5;
        ctx.stroke();

        ctx.font = 'bold 11px sans-serif';
        ctx.fillStyle = '#000000';
        ctx.textAlign = 'center';
        ctx.fillText(orderIdx + 1, nScr.x - 12, nScr.y - 8);
        ctx.textAlign = 'left';
      }
    });
  }

  // 4. Render Traverse Lines
  legs.forEach((leg, idx) => {
    var pt1 = toScreen(leg.p1.e, leg.p1.n, padding, baseScale, minE, minN);
    var pt2 = toScreen(leg.p2.e, leg.p2.n, padding, baseScale, minE, minN);
    var isSelected = (idx === selectedLegIndex || selectedLegIndices.includes(idx));

    ctx.beginPath();
    ctx.moveTo(pt1.x, pt1.y);
    ctx.lineTo(pt2.x, pt2.y);

    if (isSelected) {
      ctx.strokeStyle = '#ff00ea';
      ctx.lineWidth = 4;
    } else {
      ctx.strokeStyle = '#00f2ff';
      ctx.lineWidth = 2;
    }
    ctx.stroke();

    if (showLineData) {
      ctx.fillStyle = isSelected ? '#ff00ea' : '#ffea00';
      ctx.font = '11px monospace';
      ctx.fillText(`${leg.dmsFormatted} (${leg.dist.toFixed(3)}m)`, (pt1.x + pt2.x) / 2 + 6, (pt1.y + pt2.y) / 2 - 6);
    }
  });

  // 5. Render Box Selection
  if (isBoxSelecting && boxStart && boxCurrent) {
    var rx = Math.min(boxStart.x, boxCurrent.x);
    var ry = Math.min(boxStart.y, boxCurrent.y);
    var rw = Math.abs(boxCurrent.x - boxStart.x);
    var rh = Math.abs(boxCurrent.y - boxStart.y);

    var isWindowSelect = boxCurrent.x >= boxStart.x; 
    var isCrossingSelect = boxCurrent.x < boxStart.x; 

    if (isWindowSelect) {
      ctx.fillStyle = 'rgba(0, 102, 255, 0.2)'; 
      ctx.fillRect(rx, ry, rw, rh);
      ctx.strokeStyle = '#0066ff';
      ctx.lineWidth = 1.5;
      ctx.strokeRect(rx, ry, rw, rh);
    } else if (isCrossingSelect) {
      ctx.fillStyle = 'rgba(0, 255, 102, 0.2)'; 
      ctx.fillRect(rx, ry, rw, rh);
      ctx.strokeStyle = '#00ff66';
      ctx.lineWidth = 1.5;
      ctx.setLineDash([5, 3]); 
      ctx.strokeRect(rx, ry, rw, rh);
      ctx.setLineDash([]);
    }
  }

  // 6. Render Station Nodes & Fix Triangles
  points.forEach(pt => {
    var scr = toScreen(pt.e, pt.n, padding, baseScale, minE, minN);
    var isDatum = datumPoints.includes(pt.id);

    if (isDatum) {
      var tSize = 10;
      ctx.beginPath();
      ctx.moveTo(scr.x, scr.y - tSize - 2);
      ctx.lineTo(scr.x - tSize, scr.y + tSize - 2);
      ctx.lineTo(scr.x + tSize, scr.y + tSize - 2);
      ctx.closePath();
      
      ctx.fillStyle = '#ffea00'; 
      ctx.fill();
      ctx.strokeStyle = '#000000'; 
      ctx.lineWidth = 1.5;
      ctx.stroke();

      if (showStnLabels) {
        ctx.font = 'bold 11px sans-serif';
        ctx.strokeStyle = '#000000';
        ctx.lineWidth = 3;
        ctx.strokeText(`FIX: ${pt.id}`, scr.x - 22, scr.y - tSize - 8);
        ctx.fillStyle = '#ffea00';
        ctx.fillText(`FIX: ${pt.id}`, scr.x - 22, scr.y - tSize - 8);
      }
    } else {
      ctx.fillStyle = '#00f2ff';
      ctx.beginPath();
      ctx.arc(scr.x, scr.y, 5, 0, 2 * Math.PI);
      ctx.fill();

      if (showStnLabels) {
        ctx.font = 'bold 13px sans-serif';
        ctx.strokeStyle = '#000000';
        ctx.lineWidth = 3;
        ctx.strokeText(pt.id, scr.x + 8, scr.y + 4);
        ctx.fillStyle = '#ffffff';
        ctx.fillText(pt.id, scr.x + 8, scr.y + 4);
      }
    }
  });

  // 7. Render Snap Ring & Label
  if (snappedPoint) {
    var snapScr = toScreen(snappedPoint.e, snappedPoint.n, padding, baseScale, minE, minN);
    
    ctx.beginPath();
    ctx.arc(snapScr.x, snapScr.y, 14, 0, 2 * Math.PI);
    ctx.strokeStyle = '#00f2ff';
    ctx.lineWidth = 2.5;
    ctx.stroke();

    ctx.beginPath();
    ctx.arc(snapScr.x, snapScr.y, 20, 0, 2 * Math.PI);
    ctx.strokeStyle = 'rgba(0, 242, 255, 0.3)';
    ctx.lineWidth = 1;
    ctx.stroke();

    ctx.beginPath();
    ctx.arc(snapScr.x, snapScr.y, 4, 0, 2 * Math.PI);
    ctx.fillStyle = '#00f2ff';
    ctx.fill();

    var snapLabel = `SNAP: ${snappedPoint.id}`;
    ctx.font = 'bold 11px monospace';
    var txtWidth = ctx.measureText(snapLabel).width;

    ctx.fillStyle = 'rgba(15, 16, 22, 0.9)';
    ctx.fillRect(snapScr.x + 16, snapScr.y - 24, txtWidth + 12, 20);
    ctx.strokeStyle = '#00f2ff';
    ctx.lineWidth = 1;
    ctx.strokeRect(snapScr.x + 16, snapScr.y - 24, txtWidth + 12, 20);

    ctx.fillStyle = '#ffea00';
    ctx.fillText(snapLabel, snapScr.x + 22, snapScr.y - 10);
  }
}

/* ==========================================================================
   KDE Cadastral Survey Calculator Engine (CALCULATOR_NEWW.xls Functions)
   ========================================================================== */

/* --- Sub-Tab Switching within Calc Tab --- */
function switchCalcTool(toolKey) {
  var tools = ['traverse', 'inverse', 'missing', 'secant', 'converter'];
  tools.forEach(t => {
    var el = document.getElementById('calc-tool-' + t);
    var btn = document.getElementById('subTabCalc' + t.charAt(0).toUpperCase() + t.slice(1) + 'Btn');
    if (el) el.style.display = (t === toolKey) ? 'block' : 'none';
    if (btn) btn.classList.toggle('active', t === toolKey);
  });

  if (toolKey === 'traverse') {
    computeCurrentTraverseClosure();
  }
}

/* --- Parse DMS Angle Input (DDD.MMSS or DDD-MM-SS) --- */
function parseDmsInput(val) {
  if (typeof val === 'number') val = val.toString();
  val = (val || '').trim();
  if (!val) return 0;

  if (val.includes('-')) {
    var p = val.split('-');
    return (parseInt(p[0], 10) || 0) + ((parseInt(p[1], 10) || 0) / 60) + ((parseFloat(p[2]) || 0) / 3600);
  }
  
  var parts = val.split('.');
  var deg = parseInt(parts[0], 10) || 0;
  var frac = parts[1] || '0';
  var min = parseInt(frac.substring(0, 2), 10) || 0;
  var sec = parseFloat(frac.substring(2, 4) + (frac.length > 4 ? '.' + frac.substring(4) : '')) || 0;
  return deg + (min / 60) + (sec / 3600);
}

function formatDecimalDegreesToDMS(decDeg) {
  decDeg = (decDeg % 360 + 360) % 360;
  var deg = Math.floor(decDeg);
  var remMin = (decDeg - deg) * 60;
  var min = Math.floor(remMin);
  var sec = Math.round((remMin - min) * 60);
  if (sec === 60) { sec = 0; min += 1; }
  if (min === 60) { min = 0; deg = (deg + 1) % 360; }
  var pad = n => String(n).padStart(2, '0');
  return `${deg}°${pad(min)}'${pad(sec)}"`;
}

/* --- 1. Bowditch Traverse Misclose & Adjustment --- */
var lastBowditchAdjustment = null;

function computeCurrentTraverseClosure() {
  var reportDiv = document.getElementById('traverseClosureReport');
  var applyBtn = document.getElementById('applyBowditchBtn');
  if (!reportDiv) return;

  if (legs.length === 0) {
    reportDiv.innerHTML = `⚠️ <b>No traverse lines logged yet.</b> Add or import survey lines first.`;
    if (applyBtn) applyBtn.style.display = 'none';
    return;
  }

  var sumDist = 0;
  var sumLat = 0;
  var sumDep = 0;
  var anchorPt = points.find(p => p.id === legs[0].from) || { e: 0, n: 0 };
  var currentE = anchorPt.e;
  var currentN = anchorPt.n;

  var traverseRows = [];

  legs.forEach(leg => {
    var decDeg = leg.deg + (leg.min / 60) + (leg.sec / 3600);
    var rad = decDeg * (Math.PI / 180);
    var lat = leg.dist * Math.cos(rad);
    var dep = leg.dist * Math.sin(rad);

    sumDist += leg.dist;
    sumLat += lat;
    sumDep += dep;

    currentN += lat;
    currentE += dep;

    traverseRows.push({
      leg: leg,
      dist: leg.dist,
      lat: lat,
      dep: dep,
      rawE: currentE,
      rawN: currentN
    });
  });

  var miscloseDist = Math.hypot(sumLat, sumDep);
  var miscloseBgRad = Math.atan2(sumDep, sumLat);
  var miscloseBgDeg = (miscloseBgRad * (180 / Math.PI) + 360) % 360;
  var precisionRatio = (miscloseDist > 0.0001) ? Math.round(sumDist / miscloseDist) : 999999;

  // Compute Bowditch Adjusted Coordinates
  var adjCoords = [{ id: legs[0].from, e: anchorPt.e, n: anchorPt.n }];
  var adjE = anchorPt.e;
  var adjN = anchorPt.n;

  traverseRows.forEach((r, idx) => {
    var corrLat = -sumLat * (r.dist / sumDist);
    var corrDep = -sumDep * (r.dist / sumDist);
    var cLat = r.lat + corrLat;
    var cDep = r.dep + corrDep;

    adjN += cLat;
    adjE += cDep;

    if (idx === traverseRows.length - 1) {
      adjN = anchorPt.n;
      adjE = anchorPt.e;
    }
    adjCoords.push({ id: r.leg.to, e: adjE, n: adjN });
  });

  var geomAdj = computePolygonAreaAndPerimeter(adjCoords);

  reportDiv.innerHTML = 
    `<b>Total Line Count:</b> ${legs.length}<br>` +
    `<b>Total Perimeter:</b> ${sumDist.toFixed(3)} m (${(sumDist / LINK_TO_METER).toFixed(2)} lk)<br>` +
    `<b>Total Latitude (ΔN):</b> ${sumLat.toFixed(3)} m<br>` +
    `<b>Total Departure (ΔE):</b> ${sumDep.toFixed(3)} m<br>` +
    `<b>Linear Misclose:</b> <span style="color: #ff5566; font-weight: bold;">${miscloseDist.toFixed(4)} m</span><br>` +
    `<b>Misclose Bearing:</b> <b>${formatDecimalDegreesToDMS(miscloseBgDeg)}</b><br>` +
    `<b>Precision Ratio:</b> <span style="color: #25d366; font-weight: 800; font-size: 13px;">1 : ${precisionRatio >= 999999 ? 'Exact' : precisionRatio.toLocaleString()}</span><br>` +
    `<b>Bowditch Adjusted Area:</b> <span style="color: #ffea00; font-weight: bold;">${geomAdj.areaSqM.toFixed(2)} m² (${geomAdj.areaAc.toFixed(3)} ac / ${geomAdj.areaHa.toFixed(3)} ha)</span>`;

  if (applyBtn) applyBtn.style.display = 'block';

  lastBowditchAdjustment = {
    adjCoords: adjCoords,
    precisionRatio: precisionRatio,
    misclose: miscloseDist
  };
}

function applyBowditchAdjustment() {
  if (!lastBowditchAdjustment || !lastBowditchAdjustment.adjCoords) {
    showToast("Please compute traverse closure first!", "warning");
    return;
  }
  pushState();

  lastBowditchAdjustment.adjCoords.forEach(adj => {
    var pt = points.find(p => p.id === adj.id);
    if (pt) {
      pt.e = adj.e;
      pt.n = adj.n;
    }
  });

  relinkLegPointers();
  updateTable();
  updateStnTable();
  drawCAD();
  showToast("Bowditch corrections applied to survey stations!", "success");
}

/* --- 2. Inverse Calculator (2 Coords) --- */
function executeInverseCalc() {
  var e1 = parseFloat(document.getElementById('invE1').value);
  var n1 = parseFloat(document.getElementById('invN1').value);
  var e2 = parseFloat(document.getElementById('invE2').value);
  var n2 = parseFloat(document.getElementById('invN2').value);
  var box = document.getElementById('inverseResultBox');

  if (isNaN(e1) || isNaN(n1) || isNaN(e2) || isNaN(n2)) {
    showToast("Please enter valid coordinates for both points!", "warning");
    return;
  }

  var dE = e2 - e1;
  var dN = n2 - n1;
  var distM = Math.hypot(dE, dN);
  var distLk = distM / LINK_TO_METER;

  var rad = Math.atan2(dE, dN);
  var deg = (rad * (180 / Math.PI) + 360) % 360;

  box.style.display = 'block';
  box.innerHTML = 
    `<b>Bearing:</b> <span style="color: #00f2ff; font-weight: bold;">${formatDecimalDegreesToDMS(deg)}</span><br>` +
    `<b>Distance (m):</b> <b>${distM.toFixed(3)} m</b><br>` +
    `<b>Distance (lk):</b> <b>${distLk.toFixed(2)} lk</b><br>` +
    `<b>ΔE:</b> ${dE.toFixed(3)} m | <b>ΔN:</b> ${dN.toFixed(3)} m`;
}

/* --- 3. Missing Data Calculator --- */
function toggleMissingType() {
  var type = document.getElementById('missingTypeSelect').value;
  var dBlock = document.getElementById('missingDistancesInput');
  var bBlock = document.getElementById('missingBearingsInput');
  var box = document.getElementById('missingResultBox');
  if (box) box.style.display = 'none';

  if (type === 'distances') {
    if (dBlock) dBlock.style.display = 'block';
    if (bBlock) bBlock.style.display = 'none';
  } else {
    if (dBlock) dBlock.style.display = 'none';
    if (bBlock) bBlock.style.display = 'block';
  }
}

function executeMissingDataCalc() {
  var type = document.getElementById('missingTypeSelect').value;
  var box = document.getElementById('missingResultBox');

  var baseE = parseFloat(document.getElementById('missBaseE').value);
  var baseN = parseFloat(document.getElementById('missBaseN').value);

  // If closing baseline input is empty, automatically compute from current traverse
  if (isNaN(baseE) || isNaN(baseN)) {
    if (legs.length > 0) {
      var sumLat = 0;
      var sumDep = 0;
      legs.forEach(leg => {
        var rad = (leg.deg + (leg.min / 60) + (leg.sec / 3600)) * (Math.PI / 180);
        sumLat += leg.dist * Math.cos(rad);
        sumDep += leg.dist * Math.sin(rad);
      });
      baseE = -sumDep;
      baseN = -sumLat;
      document.getElementById('missBaseE').value = baseE.toFixed(3);
      document.getElementById('missBaseN').value = baseN.toFixed(3);
      showToast("Auto-computed baseline from logged lines.", "info");
    } else {
      showToast("Please enter the closing baseline ΔE and ΔN!", "warning");
      return;
    }
  }

  if (type === 'distances') {
    var bg1Str = document.getElementById('missBg1').value;
    var bg2Str = document.getElementById('missBg2').value;
    if (!bg1Str || !bg2Str) {
      showToast("Please enter Line 1 and Line 2 bearings (DDD.MMSS)!", "warning");
      return;
    }

    var deg1 = parseDmsInput(bg1Str);
    var deg2 = parseDmsInput(bg2Str);
    var r1 = deg1 * (Math.PI / 180);
    var r2 = deg2 * (Math.PI / 180);

    // Solve 2x2 linear system:
    // d1*sin(r1) + d2*sin(r2) = baseE
    // d1*cos(r1) + d2*cos(r2) = baseN
    var det = Math.sin(r1) * Math.cos(r2) - Math.cos(r1) * Math.sin(r2);
    if (Math.abs(det) < 0.000001) {
      showToast("Lines are parallel or collinear; no intersection exists!", "warning");
      return;
    }

    var d1 = (baseE * Math.cos(r2) - baseN * Math.sin(r2)) / det;
    var d2 = (Math.sin(r1) * baseN - Math.cos(r1) * baseE) / det;

    box.style.display = 'block';
    box.innerHTML = 
      `<b>Computed Distance 1:</b> <span style="color: #25d366; font-weight: bold;">${d1.toFixed(3)} m</span> (${(d1 / LINK_TO_METER).toFixed(2)} lk)<br>` +
      `<b>Computed Distance 2:</b> <span style="color: #25d366; font-weight: bold;">${d2.toFixed(3)} m</span> (${(d2 / LINK_TO_METER).toFixed(2)} lk)<br>` +
      `<span style="font-size: 10px; color: #8a8d9b;">*Positive values indicate forward direction along inputted bearing.</span>`;

  } else {
    // Two Missing Bearings
    var dist1 = parseFloat(document.getElementById('missDist1').value);
    var dist2 = parseFloat(document.getElementById('missDist2').value);
    if (isNaN(dist1) || isNaN(dist2) || dist1 <= 0 || dist2 <= 0) {
      showToast("Please enter valid positive distances for Line 1 and Line 2!", "warning");
      return;
    }

    var cDist = Math.hypot(baseE, baseN);
    var cBgRad = Math.atan2(baseE, baseN);

    // Triangle law of cosines: cDist, dist1, dist2
    if (dist1 + dist2 < cDist || Math.abs(dist1 - dist2) > cDist) {
      showToast("Triangle cannot close with the given lengths!", "warning");
      return;
    }

    var cosAngle1 = (dist1 * dist1 + cDist * cDist - dist2 * dist2) / (2 * dist1 * cDist);
    cosAngle1 = Math.max(-1, Math.min(1, cosAngle1));
    var angle1 = Math.acos(cosAngle1);

    var bgA1 = ((cBgRad + angle1) * (180 / Math.PI) + 360) % 360;
    var bgB1 = ((cBgRad - angle1) * (180 / Math.PI) + 360) % 360;

    box.style.display = 'block';
    box.innerHTML = 
      `<b>Solution 1:</b> Line 1 = <b>${formatDecimalDegreesToDMS(bgA1)}</b><br>` +
      `<b>Solution 2:</b> Line 1 = <b>${formatDecimalDegreesToDMS(bgB1)}</b>`;
  }
}

/* --- 4. Secant Line / Road Reserve Calculator --- */
function executeSecantCalc() {
  var b1Val = document.getElementById('secantBg1').value;
  var b2Val = document.getElementById('secantBg2').value;
  var widthVal = parseFloat(document.getElementById('secantWidth').value);
  var box = document.getElementById('secantResultBox');

  if (!b1Val || !b2Val || isNaN(widthVal) || widthVal <= 0) {
    showToast("Please enter valid Incoming Bearing, Outgoing Bearing, and Road Width!", "warning");
    return;
  }

  var theta1 = parseDmsInput(b1Val);
  var theta2 = parseDmsInput(b2Val);

  var delta = Math.abs(theta2 - theta1);
  if (delta > 180) delta = 360 - delta;

  var halfDeltaRad = (delta / 2) * (Math.PI / 180);
  if (Math.sin(halfDeltaRad) === 0) {
    showToast("Straight boundary (deflection angle is zero)!", "warning");
    return;
  }

  var secantDist = widthVal / Math.sin(halfDeltaRad);
  var bisectorBearing = ((theta1 + theta2) / 2 + 360) % 360;

  box.style.display = 'block';
  box.innerHTML = 
    `<b>Secant Cut Distance:</b> <span style="color: #25d366; font-weight: 800; font-size: 13px;">${secantDist.toFixed(3)} m</span> (${(secantDist / LINK_TO_METER).toFixed(2)} lk)<br>` +
    `<b>Deflection Angle (Δ):</b> ${delta.toFixed(4)}°<br>` +
    `<b>Bisector Bearing:</b> <b>${formatDecimalDegreesToDMS(bisectorBearing)}</b>`;
}

/* --- 5. Area Converter & Mean Bearing --- */
function convertAreaFrom(source) {
  var sqMEl = document.getElementById('convSqM');
  var haEl = document.getElementById('convHa');
  var acEl = document.getElementById('convAc');
  var sqFtEl = document.getElementById('convSqFt');

  var val = 0;
  if (source === 'm2') val = parseFloat(sqMEl.value) || 0;
  else if (source === 'ha') val = (parseFloat(haEl.value) || 0) * 10000;
  else if (source === 'ac') val = (parseFloat(acEl.value) || 0) * 4046.8564224;
  else if (source === 'ft2') val = (parseFloat(sqFtEl.value) || 0) / 10.7639104;

  if (source !== 'm2') sqMEl.value = val ? val.toFixed(3) : '';
  if (source !== 'ha') haEl.value = val ? (val / 10000).toFixed(5) : '';
  if (source !== 'ac') acEl.value = val ? (val / 4046.8564224).toFixed(5) : '';
  if (source !== 'ft2') sqFtEl.value = val ? (val * 10.7639104).toFixed(2) : '';
}

function executeMeanBearingCalc() {
  var b1Val = document.getElementById('meanBg1').value;
  var b2Val = document.getElementById('meanBg2').value;
  var box = document.getElementById('meanResultBox');

  if (!b1Val || !b2Val) {
    showToast("Please enter both Forward and Back bearings (DDD.MMSS)!", "warning");
    return;
  }

  var bg1 = parseDmsInput(b1Val);
  var bg2 = parseDmsInput(b2Val);

  // Normalize back bearing by reversing 180°
  var bg2Rev = (bg2 < 180) ? (bg2 + 180) : (bg2 - 180);

  // Circular mean
  var diff = bg2Rev - bg1;
  if (diff > 180) diff -= 360;
  if (diff < -180) diff += 360;

  var meanBg = (bg1 + diff / 2 + 360) % 360;

  box.style.display = 'block';
  box.innerHTML = 
    `<b>Mean Bearing:</b> <span style="color: #ffea00; font-weight: 800; font-size: 13px;">${formatDecimalDegreesToDMS(meanBg)}</span><br>` +
    `Forward: ${formatDecimalDegreesToDMS(bg1)} | Back Rev: ${formatDecimalDegreesToDMS(bg2Rev)}`;
}