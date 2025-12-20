// ROI Override Tool - Pure JavaScript implementation
// Processes DICOM CT series with RTSTRUCT to burn in ROI contours

let ctFiles = [];
let rtstructFile = null;
// Multi-series support
let ctSeriesMap = {}; // SeriesInstanceUID -> { seriesUID, desc, slices: [ctFile] }
let rtstructFiles = []; // list of {file,dataSet,arrayBuffer,byteArray, refSeriesUID}
let roiData = [];
let selectedROIs = [];
let roiSettings = [];
// In-memory RTSTRUCT marks (replaces BlueLight RTSSMarks)
// Each mark: { sop: string, showName: string, hideName: string, color?: string, type: 'RTSS', pointArray: [{x,y,z}] }
let RTSSMarks = [];
let roiMasks = {}; // cache: roiName -> { mask: Uint8Array, width, height, depth, bbox }
let roiContoursSag = {}; // roiName -> Map(sliceX -> segments)
let roiContoursCor = {}; // roiName -> Map(sliceY -> segments)
// Tab + MR padding workflow state
let activeTab = 'rt';
let mrSeries = [];
let mrSeriesMap = {};
let mrRegistration = null;
let mrResampledSlices = [];
let mrBlendedSlices = [];
let mrPreviewActive = false;
let mrVolume = null;
let mrStats = null;
let mrSelectedSeriesUID = null;
let currentCTSeries = null;
let currentMRSeries = null;
let mrRegistrations = [];
let mrToCtMatrix = null;
let mrBlendFraction = 1.0; // 0=CT, 1=MR
let ctWindowRange = { min: -160, max: 240 }; // defaults from 400/40
let mrWindowRange = { min: -200, max: 800 };
let ctDefaultWindowRange = { min: -160, max: 240 };
let mrDefaultWindowRange = null;
let mrWindowRebuildTimer = null;

// Prevent external hooks from throwing (no-op placeholders)
window.refreshMarkFromSeries = window.refreshMarkFromSeries || function(){};
window.refreshMark = window.refreshMark || function(){};

// Initialize line width defaults and sync to style selection
(function initLineControlsDefaults() {
    try {
        const slider = document.getElementById('lineWidth');
        const label = document.getElementById('widthValue');
        const solid = document.getElementById('styleSolid');
        const dotted = document.getElementById('styleDotted');
        if (!slider || !label) return;

        const updateLabel = () => { label.textContent = `${slider.value}px`; };

        const updatePreviewFromControls = () => {
            const sel = document.querySelector('input[name="lineStyle"]:checked');
            const styleVal = sel ? sel.value : 'solid';
            const lwVal = parseInt(slider.value || (styleVal === 'dotted' ? 2 : 1));
            const defaultHU = document.getElementById('defaultHU');
            window.previewSettings = {
                lineWidth: lwVal,
                lineStyle: styleVal,
                defaultHU: defaultHU ? parseInt(defaultHU.value) : 1000
            };
            refreshPreviewIfActive();
        };

        const getCurrentStyle = () => {
            const sel = document.querySelector('input[name="lineStyle"]:checked');
            return sel ? sel.value : 'solid';
        };

        // Set initial default based on current style
        const initialStyle = getCurrentStyle();
        slider.value = (initialStyle === 'dotted') ? 2 : 1;
        updateLabel();

        const onStyleChange = () => {
            const st = getCurrentStyle();
            slider.value = (st === 'dotted') ? 2 : 1;
            updateLabel();
            updatePreviewFromControls();
        };

        solid && solid.addEventListener('change', onStyleChange);
        dotted && dotted.addEventListener('change', onStyleChange);
        slider && slider.addEventListener('input', () => { updateLabel(); updatePreviewFromControls(); });
        const defaultHUInput = document.getElementById('defaultHU');
        defaultHUInput && defaultHUInput.addEventListener('change', updatePreviewFromControls);
    } catch (e) {
        console.warn('initLineControlsDefaults failed:', e);
    }
})();

// Preview mode state
window.previewMode = false;
window.previewOverlays = [];

let previewIsRealBurn = false;
let previewBurnedCTData = [];
let previewVolumeData = null;
let previewRestoreState = null;
let previewRestoreToggle = null;
let previewRegenTimer = null;

// Tab switching between RT burn and MR padding
function switchTab(tab) {
    const target = (tab === 'mr') ? 'mr' : 'rt';
    activeTab = target;
    const rtBtn = document.getElementById('tabRtBtn');
    const mrBtn = document.getElementById('tabMrBtn');
    rtBtn && rtBtn.classList.toggle('active', target === 'rt');
    mrBtn && mrBtn.classList.toggle('active', target === 'mr');

    const rtStruct = document.getElementById('rtStructureSection');
    if (rtStruct) rtStruct.style.display = (target === 'rt') ? 'block' : 'none';
    const mrSummary = document.getElementById('mrSummarySection');
    if (mrSummary) mrSummary.style.display = (target === 'mr') ? 'block' : 'none';
    const rtControls = document.getElementById('rtControls');
    if (rtControls) rtControls.style.display = (target === 'rt') ? 'block' : 'none';
    const mrControls = document.getElementById('mrControls');
    if (mrControls) mrControls.style.display = (target === 'mr') ? 'block' : 'none';
    const label = document.getElementById('controlsViewportLabel');
    if (label) label.textContent = (target === 'mr') ? 'MR Padding Controls' : 'Burn-In Controls';
    if (target === 'mr') {
        const out = document.getElementById('mrOutputName');
        if (out && !out.value) out.value = MR_DEFAULT_OUTPUT_NAME;
    }
    const uploadTitle = document.getElementById('ctUploadTitle');
    const uploadHint = document.getElementById('ctUploadHint');
    if (target === 'mr') {
        if (uploadTitle) uploadTitle.textContent = 'Drop CT + MR + REG DICOM here';
        if (uploadHint) uploadHint.textContent = 'Single folder or selection containing CT, MR, and rigid REG (SRO) files';
        const blendSlider = document.getElementById('mrBlendSlider');
        const blendValue = document.getElementById('mrBlendValue');
        if (blendSlider) blendSlider.value = Math.round(mrBlendFraction * 100);
        if (blendValue) blendValue.textContent = `${Math.round(mrBlendFraction * 100)}% MR`;
        const blendRow = document.getElementById('mrBlendRow');
        if (blendRow) blendRow.style.display = 'flex';
        const normToggle = document.getElementById('mrUseNormalization');
        if (normToggle) {
            normToggle.checked = false;
            normToggle.disabled = true;
            normToggle.title = 'MR uses raw intensities (normalization disabled)';
        }
        syncWindowInputsToActiveTab();
        applyWindowForActiveTab();
        const mrRow = document.getElementById('mrWindowRow');
        const ctRow = document.getElementById('ctWindowRow');
        if (mrRow) mrRow.style.display = 'none'; // MR WL hidden; display uses CT
        if (ctRow) ctRow.style.display = 'flex';
    } else {
        if (uploadTitle) uploadTitle.textContent = 'Drop CT + RS DICOM here';
        if (uploadHint) uploadHint.textContent = 'or click to browse CT + RS';
        const blendRow = document.getElementById('mrBlendRow');
        if (blendRow) blendRow.style.display = 'none';
        const mrRow = document.getElementById('mrWindowRow');
        if (mrRow) mrRow.style.display = 'none'; // RT burn only needs CT window control
        const ctRow = document.getElementById('ctWindowRow');
        if (ctRow) ctRow.style.display = 'flex';
    }

    // Avoid RT preview artifacts when switching tabs
    if (target === 'mr' && window.previewMode) {
        clearPreview();
    }

    // Toggle preview banner text for MR if needed
    const banner = document.getElementById('previewBanner');
    if (banner) banner.textContent = (target === 'mr') ? 'MR Pad Preview' : 'Preview Mode';

    // Refresh viewer for the active tab
    syncWindowInputsToActiveTab();
    applyWindowForActiveTab();
    displaySimpleViewer();
    refreshMrStatusUI();
}

// DICOM Tag constants
const Tag = {
    StudyInstanceUID: 'x0020000d',
    SeriesInstanceUID: 'x0020000e',
    SOPInstanceUID: 'x00080018',
    Modality: 'x00080060',
    PatientID: 'x00100020',
    PatientName: 'x00100010',
    StudyDate: 'x00080020',
    Rows: 'x00280010',
    Columns: 'x00280011',
    PixelSpacing: 'x00280030',
    ImagePositionPatient: 'x00200032',
    ImageOrientationPatient: 'x00200037',
    FrameOfReferenceUID: 'x00200052',
    RescaleIntercept: 'x00281052',
    RescaleSlope: 'x00281053',
    WindowCenter: 'x00281050',
    WindowWidth: 'x00281051',
    BitsAllocated: 'x00280100',
    PixelRepresentation: 'x00280103',
    ROIContourSequence: 'x30060039',
    StructureSetROISequence: 'x30060020',
    ROINumber: 'x30060022',
    ROIDisplayColor: 'x3006002a',
    ContourSequence: 'x30060040',
    ContourImageSequence: 'x30060016',
    ContourData: 'x30060050',
    ReferencedSOPInstanceUID: 'x00081155',
    ROIName: 'x30060026',
    ReferencedROINumber: 'x30060084'
};

function isRegistrationDataset(dataSet) {
    try {
        const modality = dataSet?.string?.(Tag.Modality);
        if (modality && modality.toUpperCase() === 'REG') return true;
    } catch (e) { /* ignore */ }
    try {
        const sop = dataSet?.string?.('x00080016');
        if (sop && sop.startsWith('1.2.840.10008.5.1.4.1.1.66')) return true;
    } catch (e) { /* ignore */ }
    try {
        if (dataSet?.elements?.x00700308) return true; // RegistrationSequence
    } catch (e) { /* ignore */ }
    return false;
}

function parseRegistrationForList(dataSet) {
    const list = [];
    try {
        const seq = dataSet?.elements?.x00700308?.items || [];
        seq.forEach(item => {
            const forVal = item.dataSet?.string?.('x00200052');
            if (forVal) list.push(forVal);
        });
    } catch (e) { /* ignore */ }
    return list;
}

function parseRegistrationTransforms(dataSet) {
    const transforms = [];
    const parseVal = (val) => {
        if (Array.isArray(val)) {
            const arr = val.map(v => parseFloat(v)).filter(Number.isFinite);
            return arr.length === 16 ? arr : null;
        }
        if (typeof val === 'string') {
            const arr = val.split('\\').map(v => parseFloat(v)).filter(Number.isFinite);
            return arr.length === 16 ? arr : null;
        }
        return null;
    };
    try {
        const regSeq = dataSet?.elements?.x00700308?.items || [];
        for (const item of regSeq) {
            const forUID = item.dataSet?.string?.('x00200052') || null;
            const mrs = item.dataSet?.elements?.x00700309?.items || [];
            for (const mi of mrs) {
                const mseq = mi.dataSet?.elements?.x0070030a?.items || [];
                for (const mat of mseq) {
                    const ds = mat.dataSet;
                    let matArr = null;
                    if (ds?.elements?.x300600c6) {
                        matArr = parseVal(ds.string?.('x300600c6')) || parseVal(ds.elements.x300600c6.value);
                    }
                    if (!matArr) matArr = parseVal(ds?.string?.('x0070030c'));
                    if (matArr) {
                        transforms.push({ forUID, matrix: matArr });
                        continue;
                    }
                }
            }
        }
    } catch (e) { /* ignore */ }
    return transforms;
}

// HU Presets
const HU_PRESETS = {
    "Air (-1000 HU)": -1000,
    "Water (0 HU)": 0,
    "Bolus (50 HU)": 50,
    "Titanium (7000 HU)": 7000,
    "Co-Cr-Mo (10000 HU)": 10000,
    "Stainless Steel (11000 HU)": 11000,
    "Manual Entry": null
};

// Debug toggle
const DEBUG = false;
const VERSION_DEFAULT = '1.3';
const MR_DEFAULT_OUTPUT_NAME = 'CT_MRPad_v1.3';

const TEXT_FONT_PT_DEFAULT = 12;
// Reduce footer font size by ~2 points (~2.67 px from previous 18px -> ~15px)
const FOOTER_FONT_PX = 15;
const FOOTER_MARGIN = 8;
const FOOTER_DELTA_HU = 120;
const FOOTER_TEXT_HU = 1000;

function ptToPx(pt) {
    return Math.max(6, Math.round(pt * 96 / 72));
}

function parseHuDelta(raw, fallback) {
    if (raw === null || raw === undefined) return fallback;
    let str = String(raw).trim();
    if (!str) return fallback;
    str = str.replace(/hu$/i, '').replace(/\s+/g, '');
    const value = parseFloat(str);
    return Number.isFinite(value) ? value : fallback;
}

function getFooterNoteText() {
    const el = document.getElementById('footerNote');
    if (!el) return '';
    const lines = String(el.value || '').split(/\r?\n/).slice(0, 5);
    return lines.join('\n').trim();
}

// Build default series name like CT_MMDDYY_Burn
function getDefaultSeriesName() {
    try {
        let dateStr = null;
        if (ctFiles && ctFiles.length > 0 && ctFiles[0].dataSet) {
            const ds = ctFiles[0].dataSet;
            const studyDate = ds.string(Tag.StudyDate);
            if (studyDate && studyDate.length >= 8) {
                dateStr = studyDate;
            }
        }
        if (!dateStr) {
            const d = new Date();
            const yyyy = d.getFullYear();
            const mm = String(d.getMonth() + 1).padStart(2, '0');
            const dd = String(d.getDate()).padStart(2, '0');
            dateStr = `${yyyy}${mm}${dd}`;
        }
        const mm = dateStr.slice(4, 6);
        const dd = dateStr.slice(6, 8);
        const yy = dateStr.slice(2, 4);
        return `CT_${mm}${dd}${yy}_Burn`;
    } catch (e) {
        return 'CT_Burn';
    }
}

let mrSeriesSelectResolver = null;
function openMrSeriesModal(options) {
    return new Promise((resolve) => {
        const overlay = document.getElementById('mrSeriesModal');
        const list = document.getElementById('mrSeriesList');
        if (!overlay || !list) return resolve(null);
        list.innerHTML = '';
        options.forEach(opt => {
            const btn = document.createElement('button');
            btn.className = 'mr-series-option';
            btn.innerHTML = `${opt.desc || 'MR Series'}<span class="mr-series-meta">Slices: ${opt.slices}</span>`;
            btn.onclick = () => {
                closeMrSeriesModal();
                resolve(opt.uid);
            };
            list.appendChild(btn);
        });
        overlay.style.display = 'flex';
        mrSeriesSelectResolver = resolve;
    });
}
function closeMrSeriesModal() {
    const overlay = document.getElementById('mrSeriesModal');
    if (overlay) overlay.style.display = 'none';
    if (mrSeriesSelectResolver) {
        mrSeriesSelectResolver(null);
        mrSeriesSelectResolver = null;
    }
}

async function sniffModalities(files, limit = Infinity) {
    const found = new Set();
    const slice = (limit === Infinity) ? files : files.slice(0, limit);
    for (const file of slice) {
        try {
            const buf = await file.arrayBuffer();
            const byteArray = new Uint8Array(buf);
            const ds = dicomParser.parseDicom(byteArray);
            const mod = ds?.string?.(Tag.Modality);
            if (mod) found.add(mod.toUpperCase());
            if (found.has('MR') && found.has('CT')) break;
        } catch (e) { /* ignore */ }
    }
    return found;
}

// Handle file selection
document.getElementById('dicomFiles').addEventListener('change', async function(e) {
    const files = Array.from(e.target.files || []);
    if (files.length === 0) return;

    // If something is already loaded, confirm and clear before loading new
    const hasLoaded = (ctFiles && ctFiles.length) || (processedCTData && processedCTData.length) || window.simpleViewerData || (mrSeries && mrSeries.length);
    if (hasLoaded) {
        const ok = window.confirm('Open a new DICOM set? This will clear the current images and overlays.');
        if (!ok) { e.target.value = ''; return; }
        clearAllData();
    }

    if (activeTab === 'mr') {
        await processMRPackage(files);
    } else {
        const modalities = await sniffModalities(files);
        if (modalities.has('MR')) {
            const goMr = window.confirm('MR images detected. Switch to MR Padding workspace?');
            if (goMr) {
                clearAllData();
                switchTab('mr');
                await processMRPackage(files);
                e.target.value = '';
                return;
            } else if (!modalities.has('CT')) {
                showMessage('error', 'No CT series detected. MR requires the MR Padding tab.');
                e.target.value = '';
                return;
            }
        }
        await processDICOMFiles(files);
    }
});

function clearCanvasById(id) {
    const c = document.getElementById(id);
    if (!c) return;
    const ctx = c.getContext('2d');
    if (!ctx) return;
    ctx.clearRect(0, 0, c.width || c.clientWidth || 0, c.height || c.clientHeight || 0);
}

function clearAllData() {
    try {
        // Data/state
        ctFiles = [];
        processedCTData = [];
        rtstructFile = null;
        roiData = [];
        roiSettings = [];
        roiMasks = {};
        roiContoursSag = {};
        roiContoursCor = {};
        if (window.RTSSMarks) window.RTSSMarks.length = 0;
        window.volumeData = null;
        window.simpleViewerData = null;
        window.previewMode = false;
        window.previewOverlays = [];
        window.showBurnValidation = false;
        window.lastBurnNames = [];
        // MR padding state
        mrSeries = [];
        mrSeriesMap = {};
        mrRegistration = null;
        mrResampledSlices = [];
        mrPreviewActive = false;
        mrVolume = null;
        mrStats = null;
        mrSelectedSeriesUID = null;

        // Reset viewport state
        if (typeof viewportState !== 'undefined') {
            ['axial','sagittal','coronal'].forEach(vp => {
                if (!viewportState[vp]) return;
                viewportState[vp].zoom = 1;
                viewportState[vp].panX = 0;
                viewportState[vp].panY = 0;
            });
            viewportState.sagittal.currentSliceX = 0;
            viewportState.coronal.currentSliceY = 0;
        }

        // Clear UI
        const roiVisibilityList = document.getElementById('roiVisibilityList');
        if (roiVisibilityList) roiVisibilityList.innerHTML = '';
        const filesLoadedHeader = document.getElementById('filesLoadedHeader');
        if (filesLoadedHeader) filesLoadedHeader.textContent = 'No files loaded';
        const status = document.getElementById('statusMessage');
        if (status) status.textContent = '';
        refreshMrStatusUI();

        // Clear canvases
        clearCanvasById('viewport-axial');
        clearCanvasById('viewport-sagittal');
        clearCanvasById('viewport-coronal');

    } catch(err) {
        console.warn('clearAllData error:', err);
    }
}

async function processDICOMFiles(files) {
    ctFiles = [];
    rtstructFile = null;
    ctSeriesMap = {};
    rtstructFiles = [];
    roiData = [];
    mrResampledSlices = [];
    mrPreviewActive = false;
    mrVolume = null;
    mrStats = null;
    currentCTSeries = null;
    currentMRSeries = null;
    // Reset parsed RTSTRUCT marks
    if (window.RTSSMarks) {
        window.RTSSMarks.length = 0;
    }
    roiMasks = {};
    roiContoursSag = {};
    roiContoursCor = {};
    
    updateStatus('Processing DICOM files...');
    
    for (const file of files) {
        try {
            const arrayBuffer = await file.arrayBuffer();
            const byteArray = new Uint8Array(arrayBuffer);
            
            // Parse with dicomParser
            const dataSet = dicomParser.parseDicom(byteArray);
            
            // Get modality
            const modalityValue = dataSet.string(Tag.Modality);
            
            
            // Check modality
            if (modalityValue === 'CT') {
                if (dataSet.elements && dataSet.elements.x7fe00010) {
                    const seriesUID = dataSet.string(Tag.SeriesInstanceUID) || 'UNKNOWN';
                    const seriesDesc = dataSet.string('x0008103e') || 'CT Series';
                    const entry = {
                        file,
                        dataSet,
                        arrayBuffer,
                        byteArray
                    };
                    if (!ctSeriesMap[seriesUID]) ctSeriesMap[seriesUID] = { seriesUID, desc: seriesDesc, slices: [] };
                    ctSeriesMap[seriesUID].slices.push(entry);
                } else {
                    console.warn('CT file missing pixel data:', file.name);
                }
            } else if (modalityValue === 'RTSTRUCT' || modalityValue === 'RTSS') {
                // Capture referenced series if available
                let refSeries = null;
                try {
                    // Try RTSTRUCT reference chain
                    if (dataSet.elements.x30060010 && dataSet.elements.x30060010.items[0].dataSet
                        && dataSet.elements.x30060010.items[0].dataSet.elements.x30060012
                        && dataSet.elements.x30060010.items[0].dataSet.elements.x30060012.items[0].dataSet
                        && dataSet.elements.x30060010.items[0].dataSet.elements.x30060012.items[0].dataSet.elements.x30060014
                        && dataSet.elements.x30060010.items[0].dataSet.elements.x30060012.items[0].dataSet.elements.x30060014.items[0].dataSet) {
                        refSeries = dataSet.elements.x30060010.items[0].dataSet.elements.x30060012.items[0].dataSet.elements.x30060014.items[0].dataSet.string(Tag.SeriesInstanceUID);
                    }
                } catch (ex) { /* ignore */ }
                rtstructFiles.push({ file, dataSet, arrayBuffer, byteArray, refSeriesUID: refSeries });
            }
        } catch (error) {
            console.error('Error reading DICOM file:', file.name, error);
        }
    }
    
    // Validate files
    const seriesKeys = Object.keys(ctSeriesMap);
    if (seriesKeys.length === 0) {
        showMessage('error', 'No CT files found in the selected folder');
        return;
    }
    
    // Choose CT series
    let chosenSeriesUID = seriesKeys[0];
    if (seriesKeys.length > 1) {
        // Build prompt options
        let msg = 'Multiple CT series found. Enter number to open:\n';
        seriesKeys.forEach((uid, idx) => {
            const s = ctSeriesMap[uid];
            msg += `${idx + 1}) ${s.desc || 'CT'} | Slices: ${s.slices.length}\n`;
        });
        const ans = window.prompt(msg, '1');
        const sel = Math.max(1, Math.min(seriesKeys.length, parseInt(ans || '1')));
        chosenSeriesUID = seriesKeys[sel - 1];
    }
    // Set ctFiles to chosen series and sort
    ctFiles = ctSeriesMap[chosenSeriesUID].slices;
    
    // Select RTSTRUCT: prefer ones referencing chosen series
    let chosenRT = null;
    const rtForSeries = rtstructFiles.filter(r => r.refSeriesUID === chosenSeriesUID);
    if (rtForSeries.length === 1) {
        chosenRT = rtForSeries[0];
    } else if (rtForSeries.length > 1) {
        let msg = 'Multiple RTSTRUCTs referencing this series found. Enter number:\n';
        rtForSeries.forEach((r, idx) => {
            const label = r.dataSet.string('x30060002') || r.dataSet.string('x0008103e') || `RTSTRUCT ${idx + 1}`;
            msg += `${idx + 1}) ${label}\n`;
        });
        const ans = window.prompt(msg, '1');
        const sel = Math.max(1, Math.min(rtForSeries.length, parseInt(ans || '1')));
        chosenRT = rtForSeries[sel - 1];
    } else if (rtstructFiles.length > 0) {
        // No match to series; allow choosing from all RTSTRUCTs
        let msg = 'No RTSTRUCT explicitly referencing this series. Choose an RTSTRUCT to load (or Cancel to view CT only):\n';
        rtstructFiles.forEach((r, idx) => {
            const label = r.dataSet.string('x30060002') || r.dataSet.string('x0008103e') || `RTSTRUCT ${idx + 1}`;
            msg += `${idx + 1}) ${label}\n`;
        });
        const ans = window.prompt(msg, '');
        if (ans) {
            const sel = Math.max(1, Math.min(rtstructFiles.length, parseInt(ans)));
            chosenRT = rtstructFiles[sel - 1];
        }
    }
    if (chosenRT) rtstructFile = chosenRT; else rtstructFile = null;
    
    // Sort selected CT series by ImagePositionPatient[2] (z-position)
    ctFiles.sort((a, b) => {
        const posA = a.dataSet.string(Tag.ImagePositionPatient);
        const posB = b.dataSet.string(Tag.ImagePositionPatient);
        const zA = posA ? parseFloat(posA.split('\\')[2]) : 0;
        const zB = posB ? parseFloat(posB.split('\\')[2]) : 0;
        return zA - zB;
    });
    
    // Display patient information
    const firstCT = ctFiles[0].dataSet;
    const patientId = firstCT.string(Tag.PatientID) || '—';
    const patientName = firstCT.string(Tag.PatientName) || '—';
    const studyDate = firstCT.string(Tag.StudyDate) || '';
    
    // Update header patient info
    const headerPatientId = document.getElementById('headerPatientId');
    const headerPatientName = document.getElementById('headerPatientName');
    const headerStudyDate = document.getElementById('headerStudyDate');
    
    if (headerPatientId) headerPatientId.textContent = patientId;
    if (headerPatientName) headerPatientName.textContent = patientName;
    
    if (studyDate && studyDate.length === 8) {
        const formatted = `${studyDate.slice(0,4)}-${studyDate.slice(4,6)}-${studyDate.slice(6,8)}`;
        if (headerStudyDate) headerStudyDate.textContent = formatted;
    } else {
        if (headerStudyDate) headerStudyDate.textContent = '—';
    }
    
    const filesLoadedHeader = document.getElementById('filesLoadedHeader');
    if (filesLoadedHeader) {
        const seriesName = (ctSeriesMap[chosenSeriesUID]?.desc) ? ` [${ctSeriesMap[chosenSeriesUID].desc}]` : '';
        filesLoadedHeader.textContent = rtstructFile ? `${ctFiles.length} CT${seriesName}, 1 RTSTRUCT loaded` : `${ctFiles.length} CT${seriesName} loaded`;
    }
    updateStatus('Files loaded successfully');

    currentCTSeries = {
        seriesUID: chosenSeriesUID,
        forUID: firstCT?.string?.(Tag.FrameOfReferenceUID) || null
    };
    setDefaultCTWindow(firstCT);
    
    // Extract ROI information if RTSTRUCT provided
    if (rtstructFile) {
        extractROIData();
        const rtLabel = rtstructFile.dataSet.string('x30060002') || rtstructFile.dataSet.string('x0008103e') || 'RTSTRUCT';
        showMessage('success', `Loaded ${ctFiles.length} CT images and RTSTRUCT: ${rtLabel}`);
    } else {
        showMessage('info', `Loaded ${ctFiles.length} CT images (no RTSTRUCT)`);
    }
    
    // Initialize and display viewer immediately
    setTimeout(() => {
        openViewerForPreview();
    }, 100);

    // Ensure viewport interactions are set up after a brief delay
    setTimeout(() => {
        setupViewportInteractions();
    }, 500);

    refreshMrStatusUI();
}

function refreshMrStatusUI() {
    const setText = (id, text) => {
        const el = document.getElementById(id);
        if (el) el.textContent = text;
    };
    setText('mrCtStatus', (ctFiles && ctFiles.length) ? `CT: ${ctFiles.length} slices` : 'CT: not loaded');
    setText('mrImageStatus', (mrSeries && mrSeries.length) ? `MR: ${mrSeries.length} slices` : 'MR: not loaded');
    setText('mrRegStatus', mrRegistration ? 'Reg: loaded' : (mrRegistrations.length ? `Reg: ${mrRegistrations.length} found` : 'Reg: not loaded'));
    if (mrStats) {
        const pct = mrStats.percentileUsed || 95;
        let pctVal = mrStats[`p${pct}`];
        if ((pctVal === undefined || pctVal === null) && mrStats.percentileUsed === pct && mrStats.pCustom !== undefined) {
            pctVal = mrStats.pCustom;
        }
        const desc = (pctVal !== undefined && pctVal !== null)
            ? `Raw MR: min ${mrStats.min.toFixed(0)}, p${pct} ${pctVal.toFixed(0)}`
            : `Raw MR: min ${mrStats.min.toFixed(0)}`;
        setText('mrNormStatus', desc);
    } else {
        setText('mrNormStatus', 'Raw MR: —');
    }
    updateMrPairLink();
}

function updateMRProgress(value, text = '') {
    const fill = document.getElementById('mrProgressFill');
    if (fill) fill.style.width = `${Math.max(0, Math.min(100, value || 0))}%`;
    const txt = document.getElementById('mrProgressText');
    if (txt) txt.textContent = text || '';
}

function updateMrStatusText(message) {
    const el = document.getElementById('mrStatusText');
    if (el) el.textContent = message;
}

function onMrBlendChange(val) {
    const pct = Math.max(0, Math.min(100, parseInt(val || '0', 10)));
    mrBlendFraction = pct / 100;
    const label = document.getElementById('mrBlendValue');
    if (label) label.textContent = `${pct}% MR`;
    rebuildMrBlend();
    window.volumeData = null; // force MPR rebuild with new blend
    displaySimpleViewer();
}

function shortUID(uid) {
    if (!uid) return '—';
    const parts = String(uid).split('.');
    if (parts.length <= 3) return uid;
    return `…${parts.slice(-3).join('.')}`;
}

function updateMrPairLink() {
    const el = document.getElementById('mrPairLink');
    const listEl = document.getElementById('mrPairList');
    if (!el) return;
    const ctFor = currentCTSeries?.forUID;
    const mrFor = currentMRSeries?.forUID;
    const regFor = mrRegistration?.forList || [];
    if (!ctFor && !mrFor) {
        el.textContent = 'No CT/MR pairing yet.';
        el.style.color = 'var(--text-secondary)';
        if (listEl) listEl.textContent = '';
        return;
    }
    if (!mrRegistration) {
        el.textContent = 'CT/MR loaded. REG missing.';
        el.style.color = 'var(--warning)';
        if (listEl) listEl.textContent = '';
        return;
    }
    const ctMatch = ctFor ? regFor.includes(ctFor) : false;
    const mrMatch = mrFor ? regFor.includes(mrFor) : false;
    if (ctMatch && mrMatch) {
        el.textContent = `REG links CT FOR ${shortUID(ctFor)} ↔ MR FOR ${shortUID(mrFor)}`;
        el.style.color = 'var(--success)';
    } else {
        const regText = regFor.length ? regFor.map(shortUID).join(', ') : 'none';
        el.textContent = `REG FORs (${regText}) do not match CT ${shortUID(ctFor)} / MR ${shortUID(mrFor)}`;
        el.style.color = 'var(--error)';
    }
    if (listEl) {
        if (!mrRegistrations || mrRegistrations.length <= 1) {
            listEl.textContent = '';
        } else {
            const parts = mrRegistrations.map((r, idx) => {
                const rf = (r.forList || []).map(shortUID).join(' ↔ ') || '—';
                const hasMatrix = r.matrix || (r.transforms && r.transforms.length);
                return `#${idx + 1}: ${rf}${hasMatrix ? '' : ' (no matrix)'}`;
            });
            listEl.textContent = `Available REG links: ${parts.join(' | ')}`;
        }
    }
}

// ---- MR Padding Flow ----
async function processMRPackage(files) {
    mrSeries = [];
    mrSeriesMap = {};
    mrVolume = null;
    mrStats = null;
    mrResampledSlices = [];
    mrBlendedSlices = [];
    mrPreviewActive = false;
    mrRegistration = null;
    mrRegistrations = [];
    mrToCtMatrix = null;
    currentCTSeries = null;
    currentMRSeries = null;

    ctFiles = [];
    ctSeriesMap = {};
    roiData = [];
    if (window.RTSSMarks) window.RTSSMarks.length = 0;
    roiMasks = {};
    roiContoursSag = {};
    roiContoursCor = {};

    updateMrStatusText('Processing mixed CT/MR/REG files...');
    updateMRProgress(0, '');

    for (const file of files) {
        try {
            const arrayBuffer = await file.arrayBuffer();
        const byteArray = new Uint8Array(arrayBuffer);
        const dataSet = dicomParser.parseDicom(byteArray);
        const modalityValue = dataSet.string(Tag.Modality);
        if (modalityValue === 'CT') {
            if (dataSet.elements && dataSet.elements.x7fe00010) {
                    const seriesUID = dataSet.string(Tag.SeriesInstanceUID) || 'UNKNOWN';
                    const seriesDesc = dataSet.string('x0008103e') || 'CT Series';
                    const entry = { file, dataSet, arrayBuffer, byteArray };
                    if (!ctSeriesMap[seriesUID]) ctSeriesMap[seriesUID] = { seriesUID, desc: seriesDesc, slices: [] };
                    ctSeriesMap[seriesUID].slices.push(entry);
                }
            } else if (modalityValue === 'MR') {
                if (dataSet.elements && dataSet.elements.x7fe00010) {
                    const seriesUID = dataSet.string(Tag.SeriesInstanceUID) || 'UNKNOWN';
                    const seriesDesc = dataSet.string('x0008103e') || 'MR Series';
                    const entry = { file, dataSet, arrayBuffer, byteArray };
                    if (!mrSeriesMap[seriesUID]) mrSeriesMap[seriesUID] = { seriesUID, desc: seriesDesc, slices: [] };
                    mrSeriesMap[seriesUID].slices.push(entry);
                }
            } else if (isRegistrationDataset(dataSet)) {
                const matrix = extractRegistrationMatrix(dataSet);
                const forList = parseRegistrationForList(dataSet);
                const transforms = parseRegistrationTransforms(dataSet);
                const reg = { file, dataSet, matrix, forList, transforms };
                mrRegistrations.push(reg);
                if (!mrRegistration && (matrix || (transforms && transforms.length))) {
                    mrRegistration = reg;
                }
            }
        } catch (err) {
            console.error('Error reading DICOM file:', file?.name, err);
        }
    }

    const ctKeys = Object.keys(ctSeriesMap);
    if (!ctKeys.length) {
        showMessage('error', 'No CT series found.');
        refreshMrStatusUI();
        return;
    }
    let chosenCT = ctKeys[0];
    if (ctKeys.length > 1) {
        let msg = 'Multiple CT series found. Enter number to open:\n';
        ctKeys.forEach((uid, idx) => {
            const s = ctSeriesMap[uid];
            msg += `${idx + 1}) ${s.desc || 'CT'} | Slices: ${s.slices.length}\n`;
        });
        const ans = window.prompt(msg, '1');
        const sel = Math.max(1, Math.min(ctKeys.length, parseInt(ans || '1')));
        chosenCT = ctKeys[sel - 1];
    }
    ctFiles = sortSlicesByPosition(ctSeriesMap[chosenCT].slices);
    const firstCT = ctFiles[0]?.dataSet;
    currentCTSeries = {
        seriesUID: chosenCT,
        forUID: firstCT?.string?.(Tag.FrameOfReferenceUID) || null
    };
    if (firstCT) setDefaultCTWindow(firstCT);

    const mrKeys = Object.keys(mrSeriesMap);
    if (!mrKeys.length) {
        showMessage('error', 'No MR series found.');
        refreshMrStatusUI();
        return;
    }
    let chosenMR = mrKeys[0];
    if (mrKeys.length > 1) {
        const opts = mrKeys.map(uid => ({
            uid,
            desc: mrSeriesMap[uid]?.desc || 'MR Series',
            slices: mrSeriesMap[uid]?.slices?.length || 0
        }));
        const sel = await openMrSeriesModal(opts);
        if (sel && mrKeys.includes(sel)) {
            chosenMR = sel;
        }
    }
    mrSelectedSeriesUID = chosenMR;
    mrSeries = sortSlicesByPosition(mrSeriesMap[chosenMR].slices);
    mrVolume = buildVolumeFromSlices(mrSeries, 'MR');
    mrStats = computeVolumeStats(mrVolume, parseFloat(document.getElementById('mrNormPercentile')?.value) || 95);
    setDefaultMRWindow(mrStats, mrSeries[0]?.dataSet);
    currentMRSeries = {
        seriesUID: chosenMR,
        forUID: mrSeries[0]?.dataSet?.string?.(Tag.FrameOfReferenceUID) || null
    };

    // Choose registration that links CT and MR if available
    if (mrRegistrations.length) {
        const ctFor = currentCTSeries?.forUID;
        const mrFor = currentMRSeries?.forUID;
        const regMatch = mrRegistrations.find(r => {
            if (!r.forList || r.forList.length < 2) return false;
            const hasCT = ctFor ? r.forList.includes(ctFor) : false;
            const hasMR = mrFor ? r.forList.includes(mrFor) : false;
            return hasCT && hasMR;
        }) || mrRegistrations[0];
        mrRegistration = regMatch;
    }

    // Update header patient info using CT
    const patientId = firstCT?.string?.(Tag.PatientID) || '—';
    const patientName = firstCT?.string?.(Tag.PatientName) || '—';
    const studyDate = firstCT?.string?.(Tag.StudyDate) || '';
    if (document.getElementById('headerPatientId')) document.getElementById('headerPatientId').textContent = patientId;
    if (document.getElementById('headerPatientName')) document.getElementById('headerPatientName').textContent = patientName;
    if (studyDate && studyDate.length === 8) {
        const formatted = `${studyDate.slice(0,4)}-${studyDate.slice(4,6)}-${studyDate.slice(6,8)}`;
        const el = document.getElementById('headerStudyDate');
        if (el) el.textContent = formatted;
    }
    const filesLoadedHeader = document.getElementById('filesLoadedHeader');
    if (filesLoadedHeader) {
        const seriesName = (ctSeriesMap[chosenCT]?.desc) ? ` [${ctSeriesMap[chosenCT].desc}]` : '';
        const mrName = (mrSeriesMap[chosenMR]?.desc) ? ` [${mrSeriesMap[chosenMR].desc}]` : '';
        const regText = mrRegistration ? ' + REG' : ' (REG missing)';
        filesLoadedHeader.textContent = `${ctFiles.length} CT${seriesName}, ${mrSeries.length} MR${mrName}${regText}`;
    }

    // Reset viewer data
    processedCTData = [];
    window.volumeData = null;
    window.simpleViewerData = null;
    setTimeout(() => {
        openViewerForPreview();
    }, 100);
    setTimeout(() => setupViewportInteractions(), 500);

    // Reset blend to MR-heavy by default
    mrBlendFraction = 1.0;
    mrBlendedSlices = [];
    const blendSlider = document.getElementById('mrBlendSlider');
    const blendValue = document.getElementById('mrBlendValue');
    if (blendSlider) blendSlider.value = 100;
    if (blendValue) blendValue.textContent = '100% MR';
    const blendRow = document.getElementById('mrBlendRow');
    if (blendRow && activeTab === 'mr') blendRow.style.display = 'flex';

    refreshMrStatusUI();
    showMessage('success', 'Loaded CT + MR' + (mrRegistration ? ' + REG.' : '. REG missing.'));

    // Auto-build fused preview when CT/MR/REG are matched to allow immediate visual check
    try {
        if (mrRegistration && currentCTSeries && currentMRSeries) {
            await buildMRPreview(false);
            updateMrStatusText('Preview: fused MR→CT (auto)');
        }
    } catch (e) {
        console.warn('Auto MR preview failed:', e);
    }
}

async function loadMRSeries(files) {
    if (!files || files.length === 0) return;
    mrSeries = [];
    mrSeriesMap = {};
    mrVolume = null;
    mrStats = null;
    mrResampledSlices = [];
    mrPreviewActive = false;
    currentMRSeries = null;
    updateMrStatusText('Processing MR files...');
    updateMRProgress(0, '');

    for (const file of files) {
        try {
            const arrayBuffer = await file.arrayBuffer();
            const byteArray = new Uint8Array(arrayBuffer);
            const dataSet = dicomParser.parseDicom(byteArray);
            const modalityValue = dataSet.string(Tag.Modality);
            if (modalityValue === 'MR') {
                if (dataSet.elements && dataSet.elements.x7fe00010) {
                    const seriesUID = dataSet.string(Tag.SeriesInstanceUID) || 'UNKNOWN';
                    const seriesDesc = dataSet.string('x0008103e') || 'MR Series';
                    const entry = { file, dataSet, arrayBuffer, byteArray };
                    if (!mrSeriesMap[seriesUID]) mrSeriesMap[seriesUID] = { seriesUID, desc: seriesDesc, slices: [] };
                    mrSeriesMap[seriesUID].slices.push(entry);
                }
            }
        } catch (err) {
            console.error('Error reading MR DICOM file:', file?.name, err);
        }
    }

    const seriesKeys = Object.keys(mrSeriesMap);
    if (seriesKeys.length === 0) {
        showMessage('error', 'No MR files found in the selected folder');
        updateMrStatusText('No MR files found.');
        refreshMrStatusUI();
        return;
    }

    let chosenSeriesUID = seriesKeys[0];
    if (seriesKeys.length > 1) {
        const opts = seriesKeys.map(uid => ({
            uid,
            desc: mrSeriesMap[uid]?.desc || 'MR Series',
            slices: mrSeriesMap[uid]?.slices?.length || 0
        }));
        const sel = await openMrSeriesModal(opts);
        if (sel && seriesKeys.includes(sel)) chosenSeriesUID = sel;
    }

    mrSelectedSeriesUID = chosenSeriesUID;
    mrSeries = sortSlicesByPosition(mrSeriesMap[chosenSeriesUID].slices);
    updateStatus(`MR series loaded (${mrSeries.length} slices)`);
    updateMrStatusText('MR series loaded. Computing stats...');

    mrVolume = buildVolumeFromSlices(mrSeries, 'MR');
    mrStats = computeVolumeStats(mrVolume, parseFloat(document.getElementById('mrNormPercentile')?.value) || 95);
    setDefaultMRWindow(mrStats, mrSeries[0]?.dataSet);

    currentMRSeries = {
        seriesUID: mrSelectedSeriesUID,
        forUID: mrSeries[0]?.dataSet?.string?.(Tag.FrameOfReferenceUID) || null
    };

    refreshMrStatusUI();
    showMessage('success', `Loaded MR series (${mrSeries.length} slices).`);
    if (activeTab === 'mr') {
        window.volumeData = null;
        displaySimpleViewer();
    }
}

async function loadRegistrationFile(file) {
    if (!file) return;
    try {
        const arrayBuffer = await file.arrayBuffer();
        const byteArray = new Uint8Array(arrayBuffer);
        const dataSet = dicomParser.parseDicom(byteArray);
        const matrix = extractRegistrationMatrix(dataSet);
        if (!matrix) {
            showMessage('error', 'Registration matrix not found in DICOM');
            updateMrStatusText('Registration not found in selected file.');
            return;
        }
        const forList = parseRegistrationForList(dataSet);
        const transforms = parseRegistrationTransforms(dataSet);
        mrRegistration = { file, dataSet, matrix, forList, transforms };
        mrPreviewActive = false;
        mrResampledSlices = [];
        window.volumeData = null;
        showMessage('success', 'Registration loaded.');
        updateMrStatusText('Registration loaded. Ready to preview.');
        refreshMrStatusUI();
    } catch (err) {
        console.error('Registration load failed:', err);
        showMessage('error', 'Failed to read registration DICOM.');
        updateMrStatusText('Failed to read registration DICOM.');
    }
}

function extractRegistrationMatrix(dataSet) {
    if (!dataSet) return null;
    const parseVal = (val) => {
        if (Array.isArray(val)) {
            const arr = val.map(v => parseFloat(v)).filter(Number.isFinite);
            return arr.length === 16 ? arr : null;
        }
        if (typeof val === 'string') {
            const arr = val.split('\\').map(v => parseFloat(v)).filter(Number.isFinite);
            return arr.length === 16 ? arr : null;
        }
        return null;
    };

    // Direct lookup helpers
    const tryString = (tag) => {
        try {
            const str = dataSet.string(tag);
            const arr = parseVal(str);
            if (arr) return arr;
        } catch (e) { /* ignore */ }
        return null;
    };

    // 1) Common tags on root
    if (dataSet.elements?.x300600c6) {
        const direct = tryString('x300600c6');
        if (direct) return direct;
    }
    const candidateTags = ['x300600c6', 'x0070030a', 'x0070030c'];
    for (const tag of candidateTags) {
        const arr = tryString(tag);
        if (arr) return arr;
    }

    // 2) Walk sequences explicitly (RegistrationSequence -> MatrixRegistrationSequence -> MatrixSequence)
    try {
        const regSeq = dataSet.elements?.x00700308?.items || [];
        for (const item of regSeq) {
            const mrs = item.dataSet?.elements?.x00700309?.items || [];
            for (const mi of mrs) {
                const mseq = mi.dataSet?.elements?.x0070030a?.items || [];
                for (const mat of mseq) {
                    // 3006,00C6 inside matrix item
                    const ds = mat.dataSet;
                    if (ds?.elements?.x300600c6) {
                        const arr = parseVal(ds.string?.('x300600c6'));
                        if (arr) return arr;
                        const raw = ds.elements.x300600c6.value;
                        const arr2 = parseVal(raw);
                        if (arr2) return arr2;
                    }
                    const arr = parseVal(ds?.string?.('x0070030c'));
                    if (arr) return arr;
                }
            }
        }
    } catch (e) { /* ignore */ }

    // 3) Fallback: scan all elements for (3006,00C6)
    try {
        for (const elem of dataSet.iterall()) {
            if (elem.tag && elem.tag.toString() === '3006,00C6') {
                const arr = parseVal(elem.value);
                if (arr) return arr;
            }
        }
    } catch (e) { /* ignore */ }

    return null;
}

function parseMatrixString(val) {
    if (!val) return null;
    let arr = null;
    if (Array.isArray(val)) {
        arr = val.map(v => parseFloat(v)).filter(Number.isFinite);
    } else if (typeof val === 'string') {
        arr = val.split('\\').map(v => parseFloat(v)).filter(Number.isFinite);
    }
    if (arr && arr.length === 16) return arr;
    return null;
}

function sortSlicesByPosition(list) {
    if (!Array.isArray(list)) return [];
    const sorted = [...list];
    let normal = [0, 0, 1];
    try {
        const firstOri = list[0]?.dataSet?.string?.(Tag.ImageOrientationPatient);
        if (firstOri) {
            const vals = firstOri.split('\\').map(parseFloat);
            if (vals.length === 6) {
                const rowCos = normalizeVec3(vals.slice(0, 3));
                const colCos = normalizeVec3(vals.slice(3, 6));
                normal = normalizeVec3(cross3(rowCos, colCos));
            }
        }
    } catch (e) { /* ignore */ }
    sorted.sort((a, b) => {
        const posA = parseImagePosition(a?.dataSet);
        const posB = parseImagePosition(b?.dataSet);
        const projA = dot3(posA, normal);
        const projB = dot3(posB, normal);
        return projA - projB;
    });
    return sorted;
}

function parseImagePosition(ds) {
    try {
        const pos = (ds?.string?.(Tag.ImagePositionPatient) || '0\\0\\0').split('\\').map(parseFloat);
        if (pos.length === 3 && pos.every(Number.isFinite)) return pos;
    } catch (e) { /* ignore */ }
    return [0, 0, 0];
}

function buildVolumeFromSlices(slices, modalityLabel = 'MR') {
    if (!slices || !slices.length) return null;
    const sorted = sortSlicesByPosition(slices);
    const first = sorted[0].dataSet;
    const width = first.uint16(Tag.Columns) || 512;
    const height = first.uint16(Tag.Rows) || 512;
    const pixelSpacing = (first.string(Tag.PixelSpacing) || '1\\1').split('\\').map(parseFloat);
    const rowSpacing = pixelSpacing[0] || 1;
    const colSpacing = pixelSpacing[1] || 1;
    const orientation = (first.string(Tag.ImageOrientationPatient) || '1\\0\\0\\0\\1\\0').split('\\').map(parseFloat);
    const rowCos = normalizeVec3(orientation.slice(0, 3));
    const colCos = normalizeVec3(orientation.slice(3, 6));
    const normal = normalizeVec3(cross3(rowCos, colCos));
    const positions = sorted.map(s => parseImagePosition(s.dataSet));
    const sliceSpacing = computeSliceSpacing(positions, normal, first.floatString('x00180050') || 1.0);
    const slope = first.floatString(Tag.RescaleSlope) || 1;
    const intercept = first.floatString(Tag.RescaleIntercept) || 0;

    const scalars = new Float32Array(width * height * sorted.length);
    let offset = 0;
    sorted.forEach(slice => {
        const ds = slice.dataSet;
        const pixelDataElement = ds.elements?.x7fe00010;
        if (!pixelDataElement) { offset += width * height; return; }
        const raw = new Int16Array(slice.byteArray.buffer, pixelDataElement.dataOffset, pixelDataElement.length / 2);
        const len = Math.min(raw.length, width * height);
        for (let i = 0; i < len; i++) {
            scalars[offset + i] = raw[i] * slope + intercept;
        }
        offset += width * height;
    });

    return {
        slices: sorted,
        width,
        height,
        depth: sorted.length,
        rowSpacing,
        colSpacing,
        sliceSpacing,
        rowCos,
        colCos,
        normal,
        origin: positions[0],
        positions,
        slope,
        intercept,
        scalars,
        modality: modalityLabel
    };
}

function computeSliceSpacing(positions, normal, fallback = 1.0) {
    if (!positions || positions.length < 2) return fallback || 1.0;
    const deltas = [];
    for (let i = 1; i < positions.length; i++) {
        const prev = positions[i - 1];
        const curr = positions[i];
        const diff = [curr[0] - prev[0], curr[1] - prev[1], curr[2] - prev[2]];
        const dist = Math.abs(dot3(diff, normal));
        if (Number.isFinite(dist) && dist > 0) deltas.push(dist);
    }
    if (!deltas.length) return fallback || 1.0;
    return deltas.reduce((a, b) => a + b, 0) / deltas.length;
}

function computeVolumeStats(volume, percentile = 95) {
    if (!volume || !volume.scalars) return null;
    const data = volume.scalars;
    let min = Infinity, max = -Infinity;
    const sample = [];
    const step = Math.max(1, Math.floor(data.length / 200000));
    for (let i = 0; i < data.length; i += step) {
        const v = data[i];
        if (v < min) min = v;
        if (v > max) max = v;
        sample.push(v);
    }
    sample.sort((a, b) => a - b);
    const pctVal = (p) => {
        if (!sample.length) return 0;
        const idx = Math.min(sample.length - 1, Math.max(0, Math.round(p * (sample.length - 1))));
        return sample[idx];
    };
    const p95 = pctVal(0.95);
    const p99 = pctVal(0.99);
    const pCustom = pctVal(Math.min(0.999, Math.max(0, percentile / 100)));
    const stats = { min, max, p95, p99, pCustom, percentileUsed: percentile };
    volume.stats = stats;
    return stats;
}

function normalizeMrValue(val, stats, targetHU, percentile, useNormalization = true) {
    if (!useNormalization || !stats) return val;
    const ref = (stats.percentileUsed === percentile && Number.isFinite(stats.pCustom)) ? stats.pCustom
        : (percentile >= 99 ? stats.p99 : stats.p95);
    const span = (ref - stats.min);
    if (!Number.isFinite(span) || span === 0) return val;
    const scaled = ((val - stats.min) / span) * targetHU;
    return Math.max(-1024, Math.min(1500, scaled));
}

function buildCtGeometry() {
    if (!ctFiles || !ctFiles.length) return null;
    const slices = sortSlicesByPosition(ctFiles);
    const first = slices[0].dataSet;
    const width = first.uint16(Tag.Columns) || 512;
    const height = first.uint16(Tag.Rows) || 512;
    const pixelSpacing = (first.string(Tag.PixelSpacing) || '1\\1').split('\\').map(parseFloat);
    const rowSpacing = pixelSpacing[0] || 1;
    const colSpacing = pixelSpacing[1] || 1;
    const orientation = (first.string(Tag.ImageOrientationPatient) || '1\\0\\0\\0\\1\\0').split('\\').map(parseFloat);
    const rowCos = normalizeVec3(orientation.slice(0, 3));
    const colCos = normalizeVec3(orientation.slice(3, 6));
    const normal = normalizeVec3(cross3(rowCos, colCos));
    const positions = slices.map(s => parseImagePosition(s.dataSet));
    const sliceSpacing = computeSliceSpacing(positions, normal, first.floatString('x00180050') || 1.0);
    const slope = first.floatString(Tag.RescaleSlope) || 1;
    const intercept = first.floatString(Tag.RescaleIntercept) || 0;
    return { slices, width, height, depth: slices.length, rowSpacing, colSpacing, sliceSpacing, rowCos, colCos, normal, positions, slope, intercept };
}

function worldToVoxel(volume, point) {
    if (!volume || !point) return null;
    const origin = volume.origin || [0, 0, 0];
    const diff = [point[0] - origin[0], point[1] - origin[1], point[2] - origin[2]];
    // DICOM: row index follows colCos with row spacing; column index follows rowCos with column spacing
    const i = dot3(diff, volume.colCos) / (volume.rowSpacing || 1);
    const j = dot3(diff, volume.rowCos) / (volume.colSpacing || 1);
    const k = dot3(diff, volume.normal) / (volume.sliceSpacing || 1);
    return { i, j, k };
}

function sampleVolume(volume, i, j, k, mode = 'linear') {
    if (!volume || !volume.scalars) return null;
    const { width, height, depth, scalars } = volume;
    if (mode === 'nearest') {
        const ii = Math.round(i), jj = Math.round(j), kk = Math.round(k);
        if (ii < 0 || jj < 0 || kk < 0 || ii >= height || jj >= width || kk >= depth) return null;
        const idx = kk * width * height + ii * width + jj;
        return scalars[idx];
    }

    const i0 = Math.floor(i), j0 = Math.floor(j), k0 = Math.floor(k);
    const di = i - i0, dj = j - j0, dk = k - k0;
    if (i0 < 0 || j0 < 0 || k0 < 0 || i0 + 1 >= height || j0 + 1 >= width || k0 + 1 >= depth) return null;

    const idx = (zz, yy, xx) => zz * width * height + yy * width + xx;
    const c000 = scalars[idx(k0, i0, j0)];
    const c001 = scalars[idx(k0, i0, j0 + 1)];
    const c010 = scalars[idx(k0, i0 + 1, j0)];
    const c011 = scalars[idx(k0, i0 + 1, j0 + 1)];
    const c100 = scalars[idx(k0 + 1, i0, j0)];
    const c101 = scalars[idx(k0 + 1, i0, j0 + 1)];
    const c110 = scalars[idx(k0 + 1, i0 + 1, j0)];
    const c111 = scalars[idx(k0 + 1, i0 + 1, j0 + 1)];

    const c00 = c000 * (1 - dj) + c001 * dj;
    const c01 = c010 * (1 - dj) + c011 * dj;
    const c10 = c100 * (1 - dj) + c101 * dj;
    const c11 = c110 * (1 - dj) + c111 * dj;
    const c0 = c00 * (1 - di) + c01 * di;
    const c1 = c10 * (1 - di) + c11 * di;
    return c0 * (1 - dk) + c1 * dk;
}

function getMRControlsConfig() {
    const normToggle = document.getElementById('mrUseNormalization');
    if (normToggle) normToggle.checked = false; // always keep normalization off for raw MR scale
    const useNormalization = false;
    const targetHU = parseFloat(document.getElementById('mrTargetHU')?.value) || 600;
    const percentile = Math.max(50, Math.min(100, parseFloat(document.getElementById('mrNormPercentile')?.value) || 95));
    const interpolation = document.getElementById('mrInterpolation')?.value || 'linear';
    const matrixDir = document.querySelector('input[name="mrMatrixDir"]:checked')?.value || 'mrct';
    const outputNameInput = (document.getElementById('mrOutputName')?.value || '').trim();
    const outputName = outputNameInput || MR_DEFAULT_OUTPUT_NAME;
    return { useNormalization, targetHU, percentile, interpolation, matrixDir, outputName };
}

async function resampleMRToCT() {
    if (!ctFiles || !ctFiles.length) {
        showMessage('error', 'Load CT before MR padding.');
        updateMrStatusText('Load CT before MR padding.');
        return null;
    }
    if (!mrSeries || !mrSeries.length) {
        showMessage('error', 'Load MR series for padding.');
        updateMrStatusText('Load MR series.');
        return null;
    }
    // Choose registration and direction to map MR -> CT
    const ctFor = currentCTSeries?.forUID;
    const mrFor = currentMRSeries?.forUID;
    const composeFromTransforms = (reg) => {
        if (!reg || !reg.transforms || !ctFor || !mrFor) return null;
        const ctXform = reg.transforms.find(t => t.forUID === ctFor);
        const mrXform = reg.transforms.find(t => t.forUID === mrFor);
        if (!ctXform || !ctXform.matrix || !mrXform || !mrXform.matrix) return null;
        const invCt = invertMatrix4(ctXform.matrix);
        if (!invCt) return null;
        return multiplyMatrix4(invCt, mrXform.matrix); // MR->CT = inv(CT->reg) * (MR->reg)
    };
    const chooseRegistration = () => {
        const candidates = mrRegistrations || [];
        for (const reg of candidates) {
            const hasTransforms = reg.transforms && reg.transforms.length >= 2;
            if ((!reg.matrix && !hasTransforms) || !reg.forList || reg.forList.length < 2) continue;
            const fromFOR = reg.forList[0];
            const toFOR = reg.forList[1];
            if (fromFOR === mrFor && toFOR === ctFor) {
                const composed = composeFromTransforms(reg);
                return { reg, matrix: composed || reg.matrix, inverted: false };
            }
            if (fromFOR === ctFor && toFOR === mrFor) {
                const inv = invertMatrix4(reg.matrix);
                const composed = composeFromTransforms(reg);
                if (composed) return { reg, matrix: composed, inverted: false };
                if (inv) return { reg, matrix: inv, inverted: true };
            }
            const composed = composeFromTransforms(reg);
            if (composed) return { reg, matrix: composed, inverted: false };
        }
        // fallback: first with usable data
        const any = candidates.find(r => r.matrix || (r.transforms && r.transforms.length >= 2));
        if (any) {
            const composed = composeFromTransforms(any);
            return { reg: any, matrix: composed || any.matrix, inverted: false };
        }
        return null;
    };
    const sel = chooseRegistration();
    if (sel) {
        mrRegistration = sel.reg;
        mrToCtMatrix = sel.matrix;
    } else if (mrRegistration) {
        mrToCtMatrix = mrToCtMatrix || composeFromTransforms(mrRegistration) || mrRegistration.matrix;
    }

    if (!mrToCtMatrix) {
        showMessage('error', 'Load registration DICOM before resampling.');
        updateMrStatusText('Registration missing.');
        return null;
    }
    const regFor = mrRegistration?.forList || [];
    if (regFor.length && (ctFor || mrFor) && (!(ctFor && regFor.includes(ctFor)) || !(mrFor && regFor.includes(mrFor)))) {
        showMessage('info', 'REG FORs do not match CT/MR FORs; proceeding with provided matrix.');
    }

    const config = getMRControlsConfig();
    const ctGeom = buildCtGeometry();
    if (!ctGeom) {
        showMessage('error', 'Unable to parse CT geometry.');
        updateMrStatusText('CT geometry unavailable.');
        return null;
    }
    mrVolume = mrVolume || buildVolumeFromSlices(mrSeries, 'MR');
    if (!mrVolume) {
        showMessage('error', 'Unable to build MR volume.');
        updateMrStatusText('MR volume unavailable.');
        return null;
    }
    if (config.useNormalization && (!mrStats || mrStats.percentileUsed !== config.percentile)) {
        mrStats = computeVolumeStats(mrVolume, config.percentile);
    }

    const mrRange = mrDefaultWindowRange || mrWindowRange || { min: -Infinity, max: Infinity };
    const mrMin = Number.isFinite(mrRange.min) ? mrRange.min : -Infinity;
    const mrMax = Number.isFinite(mrRange.max) ? mrRange.max : Infinity;
    const ctMin = ctWindowRange?.min ?? -200;
    const ctMax = ctWindowRange?.max ?? 800;
    const ctSpan = Math.max(1e-3, ctMax - ctMin);
    const mrSpan = Math.max(1e-3, mrMax - mrMin);

    const regMatrix = mrToCtMatrix || composeFromTransforms(mrRegistration) || mrRegistration.matrix;
    const mrToCt = (config.matrixDir === 'mrct') ? regMatrix : invertMatrix4(regMatrix);
    const ctToMr = invertMatrix4(mrToCt);
    if (!ctToMr) {
        showMessage('error', 'Registration matrix is not invertible.');
        updateMrStatusText('Registration matrix invalid.');
        return null;
    }

    const { width, height, depth, rowSpacing, colSpacing, sliceSpacing, rowCos, colCos, normal, positions, slope, intercept } = ctGeom;
    // DICOM coordinate mapping: rows follow colCos * rowSpacing; columns follow rowCos * colSpacing
    const rowVec = colCos.map(v => v * rowSpacing);
    const colVec = rowCos.map(v => v * colSpacing);
    const normVec = normal.map(v => v * sliceSpacing);
    void normVec; // kept for parity; normVec not used directly but retained for clarity

    updateMrStatusText('Resampling MR into CT grid...');
    updateMRProgress(0, '');

    const resampled = [];
    for (let sliceIdx = 0; sliceIdx < depth; sliceIdx++) {
        const ctSlice = ctGeom.slices[sliceIdx];
        const pos = positions[sliceIdx] || positions[0];
        const pixelDataElement = ctSlice?.dataSet?.elements?.x7fe00010;
        if (!pixelDataElement) continue;
        let basePixels = null;
        try {
            basePixels = new Int16Array(ctSlice.byteArray.buffer, pixelDataElement.dataOffset, pixelDataElement.length / 2);
        } catch (e) {
            basePixels = null;
        }
        if (!basePixels) continue;

        const outHU = new Float32Array(basePixels.length);
        for (let i = 0; i < basePixels.length; i++) {
            outHU[i] = basePixels[i] * slope + intercept;
        }

        // Build base for each row to reduce repeated math
        for (let r = 0; r < height; r++) {
            const rowBaseWorld = [
                pos[0] + rowVec[0] * r,
                pos[1] + rowVec[1] * r,
                pos[2] + rowVec[2] * r
            ];
            for (let c = 0; c < width; c++) {
                const world = [
                    rowBaseWorld[0] + colVec[0] * c,
                    rowBaseWorld[1] + colVec[1] * c,
                    rowBaseWorld[2] + colVec[2] * c
                ];
                const mrWorld = applyMatrix4(ctToMr, world);
                const vox = worldToVoxel(mrVolume, mrWorld);
                if (!vox) continue;
                const val = sampleVolume(mrVolume, vox.i, vox.j, vox.k, config.interpolation || 'linear');
                if (val === null || val === undefined) continue;
                const clamped = Math.max(mrMin, Math.min(mrMax, val));
                const normVal = ctMin + ((clamped - mrMin) / mrSpan) * ctSpan;
                const idx = r * width + c;
                outHU[idx] = normVal;
            }
        }

        // Stamp warnings and provenance directly into the MR-padded preview/export
        const annotationLines = ['NOT FOR DOSE CALCULATION'];
        const ctName = ctSeriesMap?.[currentCTSeries?.seriesUID || '']?.desc || currentCTSeries?.seriesUID || 'CT';
        const mrName = mrSeriesMap?.[currentMRSeries?.seriesUID || '']?.desc || currentMRSeries?.seriesUID || 'MR';
        annotationLines.push(`CT: ${ctName}`);
        annotationLines.push(`MR: ${mrName}`);
        annotationLines.forEach((line, idx) => {
            const margin = FOOTER_MARGIN + idx * (FOOTER_FONT_PX + 4);
            stampTopLeftWarning(outHU, width, height, line, margin);
        });
        // Place clinical warning at bottom
        stampTopLeftWarning(outHU, width, height, 'NOT FOR CLINICAL USE', null, true);

        const modifiedPixelData = new Int16Array(outHU.length);
        for (let i = 0; i < outHU.length; i++) {
            modifiedPixelData[i] = Math.max(-32768, Math.min(32767, Math.round((outHU[i] - intercept) / slope)));
        }
        resampled.push({ ...ctSlice, modifiedPixelData, huData: outHU });

        updateMRProgress(((sliceIdx + 1) / depth) * 100, `Slice ${sliceIdx + 1}/${depth}`);
    }

    updateMrStatusText('MR padding ready.');
    updateMRProgress(0, '');
    refreshMrStatusUI();
    return resampled;
}

async function buildMRPreview(showToast = true) {
    const resampled = await resampleMRToCT();
    if (!resampled || !resampled.length) return false;
    mrResampledSlices = resampled;
    mrBlendedSlices = rebuildMrBlend();
    mrPreviewActive = true;
    const btn = document.getElementById('mrPreviewBtn');
    if (btn) btn.textContent = 'Preview Off';
    window.volumeData = null; // force MPR rebuild with MR data
    applyWindowForActiveTab();
    displaySimpleViewer();
    if (showToast) showMessage('info', 'Preview showing MR-padded CT (MR overrides CT where present).');
    return true;
}

async function toggleMRPreview() {
    if (mrPreviewActive) {
        mrPreviewActive = false;
        mrResampledSlices = [];
        mrBlendedSlices = [];
        const btn = document.getElementById('mrPreviewBtn');
        if (btn) btn.textContent = 'Preview MR→CT';
        window.volumeData = null;
        applyWindowForActiveTab();
        displaySimpleViewer();
        updateMrStatusText('Preview off.');
        return;
    }
    await buildMRPreview(true);
}

async function exportMRPadded() {
    // Always export full MR (100%) regardless of blend slider
    const resampled = await resampleMRToCT();
    if (!resampled || !resampled.length) return;
    mrResampledSlices = resampled;
    mrBlendedSlices = [];
    const config = getMRControlsConfig();
    const seriesDesc = `${config.outputName} | MRPad v${VERSION_DEFAULT}`;
    const folderNameOverride = `${config.outputName}`.replace(/\s+/g, '_');
    const ctSeriesName = currentCTSeries?.seriesUID || 'CT';
    const mrSeriesName = currentMRSeries?.seriesUID || 'MR';
    updateMrStatusText('Exporting MR-padded CT...');
    await exportModifiedDICOM(resampled, {
        seriesDescriptionOverride: seriesDesc,
        folderNameOverride,
        zipNameSuffix: 'MRPad',
        derivationText: 'MR padded into CT pixels (rigid registration)',
        mrContext: { ctSeriesName, mrSeriesName }
    });
    showMessage('success', 'Exported MR-padded CT series.');
    updateMrStatusText('Export complete.');
}

// Vector / matrix helpers
function dot3(a, b) { return (a[0] * b[0]) + (a[1] * b[1]) + (a[2] * b[2]); }
function cross3(a, b) { return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]; }
function normalizeVec3(v) {
    const mag = Math.sqrt(dot3(v, v)) || 1;
    return [v[0] / mag, v[1] / mag, v[2] / mag];
}
function applyMatrix4(mat, point) {
    if (!mat || mat.length !== 16) return point;
    const [x, y, z] = point;
    return [
        mat[0] * x + mat[1] * y + mat[2] * z + mat[3],
        mat[4] * x + mat[5] * y + mat[6] * z + mat[7],
        mat[8] * x + mat[9] * y + mat[10] * z + mat[11]
    ];
}
function multiplyMatrix4(a, b) {
    if (!a || !b || a.length !== 16 || b.length !== 16) return null;
    const out = new Array(16).fill(0);
    for (let row = 0; row < 4; row++) {
        for (let col = 0; col < 4; col++) {
            const idx = row * 4 + col;
            out[idx] =
                a[row * 4 + 0] * b[0 * 4 + col] +
                a[row * 4 + 1] * b[1 * 4 + col] +
                a[row * 4 + 2] * b[2 * 4 + col] +
                a[row * 4 + 3] * b[3 * 4 + col];
        }
    }
    return out;
}
function invertMatrix4(m) {
    if (!m || m.length !== 16) return null;
    const inv = [];
    inv[0] = m[5]  * m[10] * m[15] - 
             m[5]  * m[11] * m[14] - 
             m[9]  * m[6]  * m[15] + 
             m[9]  * m[7]  * m[14] +
             m[13] * m[6]  * m[11] - 
             m[13] * m[7]  * m[10];
    inv[4] = -m[4]  * m[10] * m[15] + 
              m[4]  * m[11] * m[14] + 
              m[8]  * m[6]  * m[15] - 
              m[8]  * m[7]  * m[14] - 
              m[12] * m[6]  * m[11] + 
              m[12] * m[7]  * m[10];
    inv[8] = m[4]  * m[9] * m[15] - 
             m[4]  * m[11] * m[13] - 
             m[8]  * m[5] * m[15] + 
             m[8]  * m[7] * m[13] + 
             m[12] * m[5] * m[11] - 
             m[12] * m[7] * m[9];
    inv[12] = -m[4]  * m[9] * m[14] + 
               m[4]  * m[10] * m[13] +
               m[8]  * m[5] * m[14] - 
               m[8]  * m[6] * m[13] - 
               m[12] * m[5] * m[10] + 
               m[12] * m[6] * m[9];
    inv[1] = -m[1]  * m[10] * m[15] + 
              m[1]  * m[11] * m[14] + 
              m[9]  * m[2] * m[15] - 
              m[9]  * m[3] * m[14] - 
              m[13] * m[2] * m[11] + 
              m[13] * m[3] * m[10];
    inv[5] = m[0]  * m[10] * m[15] - 
             m[0]  * m[11] * m[14] - 
             m[8]  * m[2] * m[15] + 
             m[8]  * m[3] * m[14] + 
             m[12] * m[2] * m[11] - 
             m[12] * m[3] * m[10];
    inv[9] = -m[0]  * m[9] * m[15] + 
              m[0]  * m[11] * m[13] + 
              m[8]  * m[1] * m[15] - 
              m[8]  * m[3] * m[13] - 
              m[12] * m[1] * m[11] + 
              m[12] * m[3] * m[9];
    inv[13] = m[0]  * m[9] * m[14] - 
              m[0]  * m[10] * m[13] - 
              m[8]  * m[1] * m[14] + 
              m[8]  * m[2] * m[13] + 
              m[12] * m[1] * m[10] - 
              m[12] * m[2] * m[9];
    inv[2] = m[1]  * m[6] * m[15] - 
             m[1]  * m[7] * m[14] - 
             m[5]  * m[2] * m[15] + 
             m[5]  * m[3] * m[14] + 
             m[13] * m[2] * m[7] - 
             m[13] * m[3] * m[6];
    inv[6] = -m[0]  * m[6] * m[15] + 
              m[0]  * m[7] * m[14] + 
              m[4]  * m[2] * m[15] - 
              m[4]  * m[3] * m[14] - 
              m[12] * m[2] * m[7] + 
              m[12] * m[3] * m[6];
    inv[10] = m[0]  * m[5] * m[15] - 
              m[0]  * m[7] * m[13] - 
              m[4]  * m[1] * m[15] + 
              m[4]  * m[3] * m[13] + 
              m[8]  * m[1] * m[7] - 
              m[8]  * m[3] * m[5];
    inv[14] = -m[0]  * m[5] * m[14] + 
               m[0]  * m[6] * m[13] + 
               m[4]  * m[1] * m[14] - 
               m[4]  * m[2] * m[13] - 
               m[8]  * m[1] * m[6] + 
               m[8]  * m[2] * m[5];
    inv[3] = -m[1] * m[6] * m[11] + 
              m[1] * m[7] * m[10] + 
              m[5] * m[2] * m[11] - 
              m[5] * m[3] * m[10] - 
              m[9] * m[2] * m[7] + 
              m[9] * m[3] * m[6];
    inv[7] = m[0] * m[6] * m[11] - 
             m[0] * m[7] * m[10] - 
             m[4] * m[2] * m[11] + 
             m[4] * m[3] * m[10] + 
             m[8] * m[2] * m[7] - 
             m[8] * m[3] * m[6];
    inv[11] = -m[0] * m[5] * m[11] + 
               m[0] * m[7] * m[9] + 
               m[4] * m[1] * m[11] - 
               m[4] * m[3] * m[9] - 
               m[8] * m[1] * m[7] + 
               m[8] * m[3] * m[5];
    inv[15] = m[0] * m[5] * m[10] - 
              m[0] * m[6] * m[9] - 
              m[4] * m[1] * m[10] + 
              m[4] * m[2] * m[9] + 
              m[8] * m[1] * m[6] - 
              m[8] * m[2] * m[5];

    let det = m[0] * inv[0] + m[1] * inv[4] + m[2] * inv[8] + m[3] * inv[12];
    if (det === 0 || !Number.isFinite(det)) return null;
    det = 1.0 / det;
    for (let i = 0; i < 16; i++) inv[i] = inv[i] * det;
    return inv;
}

function extractROIData() {
    const rtstruct = rtstructFile.dataSet;
    roiData = [];
    // Parse RTSTRUCT into RTSSMarks and collect ROI names
    readDicomRTSS(rtstruct);
    const roiNames = getROINameList(rtstruct);
    
    if (roiNames.length === 0) {
        showMessage('error', 'No ROI sequence found in RTSTRUCT');
        return;
    }
    
    // Get ROI colors from contour sequence
    const roiColors = extractROIColors(rtstruct);
    
    // Create ROI data from extracted names
    for (let i = 0; i < roiNames.length; i++) {
        const roiName = roiNames[i];
        roiData.push({
            number: i + 1,
            name: roiName,
            color: roiColors[i] || getDefaultROIColor(i),
            visible: true
        });
    }
    
    // Sort alphabetically by ROI name (case-insensitive) and reindex numbers
    roiData.sort((a, b) => a.name.localeCompare(b.name, undefined, { sensitivity: 'base' }));
    roiData.forEach((roi, idx) => { roi.number = idx + 1; });
    
    // Display ROIs in the sidebar visibility controls
    populateROIVisibilityList();
}

function extractROIColors(dataSet) {
    // Build a map of ROI number -> color, then return in the same order as getROINameList
    const colorByNumber = {};
    const items = dataSet?.elements?.x30060039?.items || [];
    for (const it of items) {
        const ds = it.dataSet;
        if (!ds) continue;
        const num = ds.intString?.(Tag.ReferencedROINumber) || ds.uint16?.(Tag.ReferencedROINumber) || parseInt(ds.string?.(Tag.ReferencedROINumber) || '');
        const ce = ds.elements?.x3006002a;
        if (ce) {
            try {
                const raw = String(ds.string(Tag.ROIDisplayColor) || '').trim();
                if (raw) {
                    const [r,g,b] = raw.split('\\').map(v=>parseInt(v));
                    colorByNumber[num] = `rgb(${r}, ${g}, ${b})`;
                }
            } catch {}
        }
    }
    // Map to name order
    const colors = [];
    const roiItems = dataSet?.elements?.x30060020?.items || [];
    for (const it of roiItems) {
        const ds = it.dataSet;
        const num = ds?.intString?.(Tag.ROINumber) || ds?.uint16?.(Tag.ROINumber) || parseInt(ds?.string?.(Tag.ROINumber) || '');
        colors.push(colorByNumber[num] || null);
    }
    return colors;
}

function getDefaultROIColor(index) {
    const defaultColors = [
        '#ec6602', // Healthy Orange
        '#009999', // Siemens Petrol
        '#ff6b6b', // Red
        '#4ecdc4', // Teal
        '#45b7d1', // Blue
        '#96ceb4', // Green
        '#ffeaa7', // Yellow
        '#dfe6e9', // Gray
        '#a8e6cf', // Light Green
        '#ff8b94'  // Pink
    ];
    return defaultColors[index % defaultColors.length];
}

function toggleAllStructures() {
    const visibleCount = roiData.filter(r => r.visible !== false).length;
    const shouldShow = visibleCount < roiData.length / 2;
    roiData.forEach(r => { r.visible = shouldShow; });
    populateROIVisibilityList();
    updateROIOverlay();
}

function populateROIVisibilityList() {
    const roiVisibilityList = document.getElementById('roiVisibilityList');
    if (!roiVisibilityList) {
        console.error('roiVisibilityList element not found');
        return;
    }

    roiVisibilityList.innerHTML = '';

    roiData.forEach((roi, index) => {
        const item = document.createElement('div');
        item.className = 'roi-visibility-item';
        // 1) Show/Hide toggle (left-most)
        const visToggle = document.createElement('label');
        visToggle.className = 'roi-vis-toggle';
        visToggle.title = 'Show/Hide overlay';
        const visCheckbox = document.createElement('input');
        visCheckbox.type = 'checkbox';
        visCheckbox.className = 'roi-checkbox';
        visCheckbox.dataset.roiNumber = roi.number;
        visCheckbox.checked = roi.visible !== false;
        visCheckbox.onchange = () => { roi.visible = visCheckbox.checked; updateROIOverlay(); };
        const eyeIcon = document.createElement('span');
        eyeIcon.className = 'eye-icon';
        eyeIcon.textContent = '👁';
        visToggle.appendChild(visCheckbox);
        visToggle.appendChild(eyeIcon);

        // 2) Color + Name (click to toggle, dblclick to navigate)
        const info = document.createElement('div');
        info.className = 'roi-info';
        const colorBox = document.createElement('div');
        colorBox.className = 'roi-color';
        colorBox.style.backgroundColor = roi.color;
        const nameBtn = document.createElement('button');
        nameBtn.className = 'roi-name';
        nameBtn.textContent = roi.name;
        nameBtn.style.cursor = 'pointer';
        nameBtn.style.background = 'transparent';
        nameBtn.style.border = 'none';
        nameBtn.style.color = 'inherit';
        nameBtn.style.opacity = roi.visible ? '1' : '0.5';
        colorBox.style.opacity = roi.visible ? '1' : '0.5';
        nameBtn.onclick = (e) => {
            e.stopPropagation();
            roi.visible = !(roi.visible !== false);
            nameBtn.style.opacity = roi.visible ? '1' : '0.5';
            colorBox.style.opacity = roi.visible ? '1' : '0.5';
            updateROIOverlay();
        };
        nameBtn.ondblclick = (e) => { e.stopPropagation(); goToROI(roi.name); };
        info.appendChild(colorBox);
        info.appendChild(nameBtn);

        // 3) Burn/Skip toggle (selection for burn-in)
        const burnToggle = document.createElement('label');
        burnToggle.className = 'roi-toggle';
        const burnCheckbox = document.createElement('input');
        burnCheckbox.type = 'checkbox';
        burnCheckbox.className = 'roi-select-check';
        burnCheckbox.id = `roi-select-${index}`;
        burnCheckbox.checked = roi.selected || false;
        burnCheckbox.onchange = () => {
            roi.selected = burnCheckbox.checked;
            item.classList.toggle('selected', roi.selected);
            updateBurnInList();
            try {
                const anySelected = roiData.some(r => r.selected);
                if (!anySelected && window.previewMode) {
                    clearPreview();
                } else {
                    window.previewSettings = getLivePreviewSettings();
                    refreshPreviewIfActive();
                }
            } catch (e) { /* no-op */ }
        };
        const burnSlider = document.createElement('span');
        burnSlider.className = 'roi-toggle-slider';
        burnToggle.title = 'Include in burn-in';
        burnToggle.appendChild(burnCheckbox);
        burnToggle.appendChild(burnSlider);

        // Row click toggles visibility (display/hide). Selection remains on the toggle.
        item.addEventListener('click', (e) => {
            // Ignore clicks on the burn/skip toggle itself
            if (e.target === burnCheckbox || e.target === burnSlider) return;
            // Toggle visibility
            roi.visible = !(roi.visible !== false);
            nameBtn.style.opacity = roi.visible ? '1' : '0.5';
            colorBox.style.opacity = roi.visible ? '1' : '0.5';
            updateROIOverlay();
        });

        item.appendChild(info);
        item.appendChild(burnToggle);

        roiVisibilityList.appendChild(item);
    });

    updateBurnInList();
}

function updateBurnInList() {
    // This function updates the burn-in controls based on selected ROIs
    const selectedROIs = roiData.filter(roi => roi.selected);
    
    // Update burn-in panel with selected ROIs count
    const burnPanel = document.querySelector('.burn-controls');
    if (burnPanel) {
        let countLabel = document.getElementById('selectedROICount');
        if (!countLabel) {
            const label = document.createElement('div');
            label.id = 'selectedROICount';
            label.className = 'selected-count';
            label.textContent = `Selected ROIs: ${selectedROIs.length}`;
            const controlPanel = burnPanel.querySelector('.control-panel');
            if (controlPanel) {
                const firstControl = controlPanel.querySelector('.control-row');
                if (firstControl && firstControl.parentNode === controlPanel) {
                    controlPanel.insertBefore(label, firstControl);
                } else {
                    controlPanel.appendChild(label);
                }
            }
        } else {
            countLabel.textContent = `Selected ROIs: ${selectedROIs.length}`;
        }
    }

    // Populate per-ROI override list for selected structures
    const overridesRow = document.getElementById('perRoiOverridesRow');
    const listContainer = document.getElementById('roiConfigList');
    if (overridesRow && listContainer) {
        const hasOverrides = selectedROIs.length > 0;
        overridesRow.style.display = hasOverrides ? 'flex' : 'none';
        listContainer.innerHTML = '';

        if (hasOverrides) {
            const globalFill = parseHuDelta(document.getElementById('fillPercent')?.value ?? -100, -100);
            const globalWidth = parseFloat(document.getElementById('lineWidth')?.value || '2');
            const fillEnabled = !!document.getElementById('enableFill')?.checked;

            selectedROIs.forEach(roi => {
                if (typeof roi.lineStyleOverride === 'undefined') roi.lineStyleOverride = 'global';
                if (typeof roi.fillDeltaOverride === 'undefined' || roi.fillDeltaOverride === '') roi.fillDeltaOverride = null;
                if (typeof roi.lineWidthOverride === 'undefined' || roi.lineWidthOverride === '') roi.lineWidthOverride = null;

                const item = document.createElement('div');
                item.className = 'roi-config-item';

                const left = document.createElement('div');
                left.style.display = 'flex';
                left.style.alignItems = 'center';
                left.style.gap = '8px';
                const colorBox = document.createElement('div');
                colorBox.className = 'roi-color';
                colorBox.style.backgroundColor = roi.color || '#888';
                const nameSpan = document.createElement('div');
                nameSpan.className = 'roi-name';
                nameSpan.textContent = roi.name;
                left.appendChild(colorBox);
                left.appendChild(nameSpan);

                const right = document.createElement('div');
                right.style.display = 'flex';
                right.style.flexWrap = 'wrap';
                right.style.gap = '8px';
                right.style.alignItems = 'center';

                const styleSel = document.createElement('select');
                styleSel.className = 'preset-select';
                styleSel.title = 'Outline style';
                [{ label: 'Global', value: 'global' }, { label: 'Solid', value: 'solid' }, { label: 'Dotted', value: 'dotted' }]
                    .forEach(opt => {
                        const o = document.createElement('option');
                        o.value = opt.value;
                        o.textContent = opt.label;
                        styleSel.appendChild(o);
                    });
                styleSel.value = roi.lineStyleOverride || 'global';
                styleSel.addEventListener('change', () => {
                    roi.lineStyleOverride = styleSel.value;
                    refreshPreviewIfActive();
                });

                const widthInput = document.createElement('input');
                widthInput.type = 'number';
                widthInput.className = 'manual-input';
                widthInput.style.width = '68px';
                widthInput.step = '0.5';
                widthInput.min = '0.5';
                widthInput.max = '10';
                widthInput.placeholder = 'Line px';
                widthInput.title = 'Per-ROI contour line width (pixels)';
                const resolveWidthValue = () => {
                    const parsed = parseFloat(roi.lineWidthOverride);
                    return Number.isFinite(parsed) && parsed > 0 ? parsed : globalWidth;
                };
                widthInput.value = String(resolveWidthValue());
                const commitWidthValue = () => {
                    const raw = widthInput.value.trim();
                    if (!raw) {
                        roi.lineWidthOverride = null;
                        widthInput.value = String(globalWidth);
                        refreshPreviewIfActive();
                        return;
                    }
                    let parsed = parseFloat(raw);
                    if (!Number.isFinite(parsed)) {
                        roi.lineWidthOverride = null;
                        widthInput.value = String(globalWidth);
                        refreshPreviewIfActive();
                        return;
                    }
                    parsed = Math.max(0.5, Math.min(10, parsed));
                    parsed = Math.round(parsed * 2) / 2; // snap to 0.5 px increments
                    roi.lineWidthOverride = parsed;
                    widthInput.value = parsed.toString();
                    refreshPreviewIfActive();
                };
                widthInput.addEventListener('blur', commitWidthValue);
                widthInput.addEventListener('change', commitWidthValue);
                widthInput.addEventListener('keydown', evt => {
                    if (evt.key === 'Enter') {
                        evt.preventDefault();
                        commitWidthValue();
                    }
                });

                const fillInput = document.createElement('input');
                fillInput.type = 'number';
                fillInput.className = 'manual-input';
                fillInput.style.width = '72px';
                fillInput.step = '50';
                fillInput.min = '-1000';
                fillInput.max = '1000';
                fillInput.placeholder = 'ΔHU';
                fillInput.title = 'Per-ROI fill ΔHU (50 HU increments)';
                const resolveDisplayValue = () => {
                    if (roi.fillDeltaOverride === null || roi.fillDeltaOverride === undefined) return globalFill;
                    if (!Number.isFinite(roi.fillDeltaOverride)) return globalFill;
                    return roi.fillDeltaOverride;
                };
                fillInput.value = String(resolveDisplayValue());

                const minusBtn = document.createElement('button');
                minusBtn.type = 'button';
                minusBtn.textContent = '−';
                minusBtn.title = 'Decrease fill ΔHU by 50';
                const plusBtn = document.createElement('button');
                plusBtn.type = 'button';
                plusBtn.textContent = '+';
                plusBtn.title = 'Increase fill ΔHU by 50';
                [minusBtn, plusBtn].forEach(btn => {
                    btn.style.padding = '0 6px';
                    btn.style.height = '24px';
                    btn.style.border = '1px solid var(--input-border)';
                    btn.style.background = 'var(--input-bg)';
                    btn.style.color = 'var(--text-primary)';
                    btn.style.borderRadius = '3px';
                    btn.style.cursor = 'pointer';
                });

                const normalizeDelta = (value) => {
                    let parsed = parseFloat(value);
                    if (!Number.isFinite(parsed)) return null;
                    parsed = Math.round(parsed / 50) * 50;
                    parsed = Math.max(-1000, Math.min(1000, parsed));
                    return parsed;
                };

                const commitFillValue = () => {
                    if (!fillEnabled) {
                        fillInput.value = String(resolveDisplayValue());
                        return;
                    }
                    const raw = fillInput.value.trim();
                    if (!raw) {
                        roi.fillDeltaOverride = null;
                        fillInput.value = String(globalFill);
                        refreshPreviewIfActive();
                        return;
                    }
                    const normalized = normalizeDelta(raw);
                    if (normalized === null) {
                        roi.fillDeltaOverride = null;
                        fillInput.value = String(globalFill);
                    } else {
                        roi.fillDeltaOverride = normalized;
                        fillInput.value = String(normalized);
                    }
                    refreshPreviewIfActive();
                };

                fillInput.addEventListener('blur', commitFillValue);
                fillInput.addEventListener('change', commitFillValue);
                fillInput.addEventListener('keydown', evt => {
                    if (evt.key === 'Enter') {
                        evt.preventDefault();
                        commitFillValue();
                    }
                });

                const adjustFill = (delta) => {
                    if (!fillEnabled) return;
                    let current = resolveDisplayValue();
                    if (!Number.isFinite(current)) current = globalFill;
                    current = normalizeDelta(current + delta);
                    if (current === null) return;
                    roi.fillDeltaOverride = current;
                    fillInput.value = String(current);
                    refreshPreviewIfActive();
                };
                minusBtn.addEventListener('click', () => adjustFill(-50));
                plusBtn.addEventListener('click', () => adjustFill(50));

                const deltaWrapper = document.createElement('div');
                deltaWrapper.style.display = 'flex';
                deltaWrapper.style.alignItems = 'center';
                deltaWrapper.style.gap = '4px';
                deltaWrapper.appendChild(minusBtn);
                deltaWrapper.appendChild(fillInput);
                deltaWrapper.appendChild(plusBtn);

                const applyFillEnabledState = () => {
                    const disabled = !fillEnabled;
                    fillInput.disabled = disabled;
                    minusBtn.disabled = disabled;
                    plusBtn.disabled = disabled;
                    if (disabled) {
                        fillInput.value = String(resolveDisplayValue());
                    }
                };
                applyFillEnabledState();

                right.appendChild(styleSel);
                right.appendChild(widthInput);
                right.appendChild(deltaWrapper);

                item.appendChild(left);
                item.appendChild(right);
                listContainer.appendChild(item);
            });
        }
    }
}

// Preview burn-in without modifying data
async function previewBurnIn() {
    if (window.previewMode && previewIsRealBurn) {
        clearPreview();
        showMessage('info', 'Preview mode disabled.');
        return;
    }

    const success = await buildPreviewBurn(true);
    if (!success) {
        clearPreview();
        return;
    }

    if (!window.previewMode) window.previewMode = true;
    previewIsRealBurn = true;

    if (window.simpleViewerData) {
        previewRestoreState = window.simpleViewerData.isShowingBurned;
        window.simpleViewerData.isShowingBurned = true;
    } else {
        previewRestoreState = false;
        await initializeSimpleViewer();
        if (window.simpleViewerData) window.simpleViewerData.isShowingBurned = true;
    }

    const toggleEl = document.getElementById('toggleBurnedView');
    if (toggleEl) {
        previewRestoreToggle = { checked: toggleEl.checked, disabled: toggleEl.disabled };
        toggleEl.checked = true;
        toggleEl.disabled = true;
    }

    showMessage('info', 'Preview mode showing in-memory burned images. Click Preview again to exit.');
    displaySimpleViewer();
    setPreviewUI(true);
}

async function buildPreviewBurn(showErrors = false) {
    const config = collectBurnConfig({ suppressSelectionError: !showErrors });
    if (!config) return false;
    const { burnInSettings } = config;
    if (!burnInSettings || burnInSettings.length === 0) {
        if (showErrors) showMessage('error', 'Select at least one ROI before previewing.');
        return false;
    }
    if (!ctFiles || ctFiles.length === 0) {
        if (showErrors) showMessage('error', 'Load CT images before previewing.');
        return false;
    }

    try {
        updateStatus('Building preview...');
        updateProgress(0);
        previewBurnedCTData = burnSlices(ctFiles, burnInSettings, {
            textEnabled: false,
            textInterval: 1,
            textDeltaHU: 100,
            textFontPx: ptToPx(TEXT_FONT_PT_DEFAULT),
            footerDelta: FOOTER_DELTA_HU,
            noteText: config.noteText,
            progressCallback: (current, total) => updateProgress((current / total) * 100)
        });
        previewVolumeData = null;
        // Force MPR to rebuild from preview series
        window.volumeData = null;
        window.previewSettings = getLivePreviewSettings();
        window.previewMode = true;
        previewIsRealBurn = true;
        return true;
    } catch (err) {
        console.error('Preview generation failed:', err);
        if (showErrors) showMessage('error', `Preview failed: ${err.message || err}`);
        return false;
    } finally {
        updateStatus('');
        updateProgress(0);
    }
}

function clearPreview() {
    window.previewMode = false;
    window.previewOverlays = [];
    window.previewSettings = null;
    previewIsRealBurn = false;
    previewBurnedCTData = [];
    previewVolumeData = null;
    // no preview footer overlay; preview is exact burned pixels
    if (window.simpleViewerData) {
        window.simpleViewerData.isShowingBurned = previewRestoreState || false;
    }
    const toggleEl = document.getElementById('toggleBurnedView');
    if (toggleEl && previewRestoreToggle) {
        toggleEl.checked = !!previewRestoreToggle.checked;
        toggleEl.disabled = !!previewRestoreToggle.disabled;
    } else if (toggleEl) {
        toggleEl.disabled = false;
    }
    previewRestoreState = null;
    previewRestoreToggle = null;
    if (previewRegenTimer) {
        clearTimeout(previewRegenTimer);
        previewRegenTimer = null;
    }
    // Force MPR to rebuild from original series
    window.volumeData = null;
    setPreviewUI(false);
    displaySimpleViewer();
}

function getLivePreviewSettings() {
    if (!window.previewMode) return null;
    return {
        lineWidth: parseInt(document.getElementById('lineWidth')?.value || 2, 10),
        lineStyle: document.querySelector('input[name="lineStyle"]:checked')?.value || 'solid',
        fillEnabled: !!document.getElementById('enableFill')?.checked,
        fillDeltaHU: parseHuDelta(document.getElementById('fillPercent')?.value ?? -100, -100),
        textEnabled: false,
        textInterval: 1,
        textDeltaHU: 100,
        textFontPt: TEXT_FONT_PT_DEFAULT
    };
}

function refreshPreviewIfActive() {
    if (!window.previewMode) return;
    if (previewIsRealBurn) {
        schedulePreviewRegeneration();
    } else {
        displaySimpleViewer();
    }
}

function setPreviewUI(active) {
    const btn = document.getElementById('previewToggle');
    if (btn) {
        btn.textContent = active ? 'Preview Off' : 'Preview On';
    }
    const banner = document.getElementById('previewBanner');
    if (banner) {
        banner.style.display = active ? 'block' : 'none';
    }
}

function schedulePreviewRegeneration() {
    if (previewRegenTimer) clearTimeout(previewRegenTimer);
    previewRegenTimer = setTimeout(() => {
        previewRegenTimer = null;
        if (!window.previewMode || !previewIsRealBurn) return;
        buildPreviewBurn(false).catch(err => console.error('Preview regeneration failed:', err));
    }, 250);
}

function collectBurnConfig(options = {}) {
    const { suppressSelectionError = false } = options;

    let imageSetName = (document.getElementById('imageSetName')?.value || '').trim();
    if (!imageSetName) {
        const def = getDefaultSeriesName();
        imageSetName = def;
        const input = document.getElementById('imageSetName');
        if (input) input.value = def;
    }

    const defaultHU = parseInt(document.getElementById('defaultHU')?.value, 10);
    const resolvedDefaultHU = Number.isFinite(defaultHU) ? defaultHU : 1000;

    const lineStyleSel = document.querySelector('input[name="lineStyle"]:checked');
    const lineStyle = lineStyleSel ? lineStyleSel.value : 'solid';
    const lineWidthCtrl = document.getElementById('lineWidth');
    const lineWidth = lineWidthCtrl ? parseInt(lineWidthCtrl.value, 10) || 2 : 2;

    const fillEnabled = !!document.getElementById('enableFill')?.checked;
    const fillDeltaHU = parseHuDelta(document.getElementById('fillPercent')?.value ?? -100, -100);

    const burnInSettings = [];
    const burnNames = [];
    if (Array.isArray(roiData)) {
        roiData.forEach(roi => {
            if (!roi.selected) return;

            const roiHU = (() => {
                if (roi.huValue !== undefined && roi.huValue !== null && roi.huValue !== '') {
                    const parsed = parseFloat(roi.huValue);
                    if (Number.isFinite(parsed)) return parsed;
                }
                return resolvedDefaultHU;
            })();

            const perRoiLineStyle = (roi.lineStyleOverride && roi.lineStyleOverride !== 'global')
                ? roi.lineStyleOverride
                : lineStyle;

            let perRoiFillDelta = fillDeltaHU;
            if (fillEnabled) {
                const override = parseHuDelta(roi.fillDeltaOverride, NaN);
                if (Number.isFinite(override)) {
                    perRoiFillDelta = override;
                }
            }

            const perRoiLineWidth = (() => {
                const override = parseFloat(roi.lineWidthOverride);
                if (Number.isFinite(override) && override > 0) {
                    return override;
                }
                return lineWidth;
            })();

            burnInSettings.push({
                name: roi.name,
                number: roi.number,
                contour: true,
                fill: fillEnabled,
                fillDeltaHU: perRoiFillDelta,
                huValue: Number.isFinite(roiHU) ? roiHU : resolvedDefaultHU,
                lineStyle: perRoiLineStyle,
                lineWidth: perRoiLineWidth
            });
            burnNames.push(roi.name);
        });
    }

    if (burnInSettings.length === 0) {
        if (!suppressSelectionError) {
            showMessage('error', 'Please select at least one ROI for burn-in');
        }
        return null;
    }

    let separateSeries = false;
    try {
        const exportModeSel = document.querySelector('input[name="exportMode"]:checked');
        if (exportModeSel) {
            separateSeries = (exportModeSel.value === 'separate');
        } else if (!suppressSelectionError && burnInSettings.length > 1) {
            const oneSeries = window.confirm('Burn all selected ROIs into ONE series?\nClick Cancel to create a SEPARATE series per ROI.');
            separateSeries = !oneSeries;
        }
    } catch (err) {
        console.debug('collectBurnConfig export mode error:', err);
    }

    window.previewSettings = {
        lineWidth,
        lineStyle,
        defaultHU: resolvedDefaultHU,
        fillEnabled,
        fillDeltaHU
    };

    return {
        imageSetName,
        defaultHU: resolvedDefaultHU,
        lineStyle,
        lineWidth,
        fillEnabled,
        fillDeltaHU,
        noteText: getFooterNoteText(),
        burnInSettings,
        burnNames,
        separateSeries
    };
}

window.addEventListener('load', () => {
    const fillToggle = document.getElementById('enableFill');
    if (fillToggle) fillToggle.addEventListener('change', () => {
        updateBurnInList();
        refreshPreviewIfActive();
    });
    const fillPercent = document.getElementById('fillPercent');
    if (fillPercent) fillPercent.addEventListener('input', () => {
        updateBurnInList();
        if (!window.previewMode) return;
        if (previewIsRealBurn) schedulePreviewRegeneration();
        else refreshPreviewIfActive();
    });
    const lineWidthInput = document.getElementById('lineWidth');
    if (lineWidthInput) lineWidthInput.addEventListener('input', () => {
        updateBurnInList();
        refreshPreviewIfActive();
    });
    const footerNote = document.getElementById('footerNote');
    const footerCounter = document.getElementById('notesCharCount');
    const enforceFooterLimits = () => {
        if (!footerNote) return;
        const lines = footerNote.value.split(/\r?\n/);
        if (lines.length > 5) {
            footerNote.value = lines.slice(0, 5).join('\n');
        }
        if (footerCounter) footerCounter.textContent = `${footerNote.value.length} chars`;
    };
    if (footerNote) {
        footerNote.addEventListener('input', () => {
            enforceFooterLimits();
            if (!window.previewMode) return;
            if (previewIsRealBurn) schedulePreviewRegeneration();
            else refreshPreviewIfActive();
        });
        footerNote.addEventListener('blur', enforceFooterLimits);
        setTimeout(enforceFooterLimits, 0);
    }
});

function updateROIOverlay() {
    // Redraw the current view with updated ROI visibility
    if (window.simpleViewerData && window.simpleViewerData.currentSlice !== undefined) {
        displaySimpleViewer();
    }
}

// Draw ROI overlay on sagittal view
function drawROIOverlaySagittal(ctx, volume, sliceX, displayParams) {
    if (activeTab === 'mr') return;
    if (!RTSSMarks || RTSSMarks.length === 0) return;
    if (!roiData || roiData.length === 0) return;
    if (!displayParams) return;
    if (!volume.imagePosition || volume.imagePosition.length === 0) return;
    // During real preview, pixels are already burned into the preview series
    // and visible in the MPR. Suppress yellow overlay lines to match external behavior.
    if (window.previewMode && previewIsRealBurn) return;

    const scaleX = displayParams.displayWidth / displayParams.dataWidth;
    const scaleY = displayParams.displayHeight / displayParams.dataHeight;
    const scalePx = Math.min(scaleX, scaleY);
    const previewSettings = getLivePreviewSettings();

    roiData.forEach((roi) => {
        if (!roi.visible) return;
        const segments = getOrBuildContoursSag(roi.name, sliceX, volume);
        if (!segments || segments.length === 0) return;
        if (previewSettings && roi.selected) {
            const lwBase = previewSettings.lineWidth || 2;
            const overrideWidth = parseFloat(roi.lineWidthOverride);
            const effectiveWidth = Number.isFinite(overrideWidth) && overrideWidth > 0 ? overrideWidth : lwBase;
            const style = (roi.lineStyleOverride && roi.lineStyleOverride !== 'global')
                ? roi.lineStyleOverride
                : (previewSettings.lineStyle || 'solid');
            ctx.strokeStyle = '#ffff00';
            ctx.lineWidth = effectiveWidth * scalePx;
            ctx.globalAlpha = 0.95;
            if (style === 'dotted') {
                const gap = Math.max(4, effectiveWidth * 2.5);
                ctx.setLineDash([effectiveWidth * scalePx, gap * scalePx]);
            } else ctx.setLineDash([]);
        } else {
            ctx.strokeStyle = roi.color || '#00ff00';
            const overrideWidth = parseFloat(roi.lineWidthOverride);
            const fallbackWidth = Number.isFinite(overrideWidth) && overrideWidth > 0 ? overrideWidth : 2;
            ctx.lineWidth = fallbackWidth * scalePx;
            ctx.globalAlpha = 0.95;
            ctx.setLineDash([]);
        }
        ctx.beginPath();
        for (const seg of segments) {
            const y1 = seg[0], z1 = seg[1], y2 = seg[2], z2 = seg[3];
            const dY1 = displayParams.offsetX + y1 * scaleX;
            const dZ1 = displayParams.offsetY + (displayParams.dataHeight - 1 - z1) * scaleY;
            const dY2 = displayParams.offsetX + y2 * scaleX;
            const dZ2 = displayParams.offsetY + (displayParams.dataHeight - 1 - z2) * scaleY;
            ctx.moveTo(dY1, dZ1);
            ctx.lineTo(dY2, dZ2);
        }
        ctx.stroke();
    });
}

// Draw ROI overlay on coronal view
function drawROIOverlayCoronal(ctx, volume, sliceY, displayParams) {
    if (activeTab === 'mr') return;
    if (!RTSSMarks || RTSSMarks.length === 0) return;
    if (!roiData || roiData.length === 0) return;
    if (!displayParams) return;
    if (!volume.imagePosition || volume.imagePosition.length === 0) return;
    // During real preview, pixels are already burned into the preview series
    // and visible in the MPR. Suppress yellow overlay lines to match external behavior.
    if (window.previewMode && previewIsRealBurn) return;

    const scaleX = displayParams.displayWidth / displayParams.dataWidth;
    const scaleY = displayParams.displayHeight / displayParams.dataHeight;
    const scalePx = Math.min(scaleX, scaleY);
    const previewSettings = getLivePreviewSettings();

    roiData.forEach((roi) => {
        if (!roi.visible) return;
        const segments = getOrBuildContoursCor(roi.name, sliceY, volume);
        if (!segments || segments.length === 0) return;
        if (previewSettings && roi.selected) {
            const lwBase = previewSettings.lineWidth || 2;
            const overrideWidth = parseFloat(roi.lineWidthOverride);
            const effectiveWidth = Number.isFinite(overrideWidth) && overrideWidth > 0 ? overrideWidth : lwBase;
            const style = (roi.lineStyleOverride && roi.lineStyleOverride !== 'global')
                ? roi.lineStyleOverride
                : (previewSettings.lineStyle || 'solid');
            ctx.strokeStyle = '#ffff00';
            ctx.lineWidth = effectiveWidth * scalePx;
            ctx.globalAlpha = 0.95;
            if (style === 'dotted') {
                const gap = Math.max(4, effectiveWidth * 2.5);
                ctx.setLineDash([effectiveWidth * scalePx, gap * scalePx]);
            } else ctx.setLineDash([]);
        } else {
            ctx.strokeStyle = roi.color || '#00ff00';
            const overrideWidth = parseFloat(roi.lineWidthOverride);
            const fallbackWidth = Number.isFinite(overrideWidth) && overrideWidth > 0 ? overrideWidth : 2;
            ctx.lineWidth = fallbackWidth * scalePx;
            ctx.globalAlpha = 0.95;
            ctx.setLineDash([]);
        }
        ctx.beginPath();
        for (const seg of segments) {
            const x1 = seg[0], z1 = seg[1], x2 = seg[2], z2 = seg[3];
            const dX1 = displayParams.offsetX + x1 * scaleX;
            const dZ1 = displayParams.offsetY + (displayParams.dataHeight - 1 - z1) * scaleY;
            const dX2 = displayParams.offsetX + x2 * scaleX;
            const dZ2 = displayParams.offsetY + (displayParams.dataHeight - 1 - z2) * scaleY;
            ctx.moveTo(dX1, dZ1);
            ctx.lineTo(dX2, dZ2);
        }
        ctx.stroke();
    });
}

// Draw ROI overlays on canvas
function drawROIOverlayOnCanvas(ctx, ctData, sliceIndex, width, height, displayParams) {
    if (activeTab === 'mr') return;
    if (!RTSSMarks || RTSSMarks.length === 0) return;
    if (!roiData || roiData.length === 0) return;
    if (window.previewMode && previewIsRealBurn) return;
    
    // Get the SOP Instance UID for the current slice
    const sopUID = ctData.dataSet.string(Tag.SOPInstanceUID);
    if (!sopUID) return;
    
    // Get image position and pixel spacing for coordinate transformation
    const imagePosition = ctData.dataSet.string(Tag.ImagePositionPatient);
    const pixelSpacing = ctData.dataSet.string(Tag.PixelSpacing);
    
    if (!imagePosition || !pixelSpacing) return;
    
    const imgPos = imagePosition.split('\\').map(parseFloat);
    const pixSpacing = pixelSpacing.split('\\').map(parseFloat);
    
    // Get image orientation
    const imageOrientation = ctData.dataSet.string(Tag.ImageOrientationPatient);
    if (!imageOrientation) return;
    
    const orientation = imageOrientation.split('\\').map(parseFloat);
    const rowCosines = [orientation[0], orientation[1], orientation[2]];
    const colCosines = [orientation[3], orientation[4], orientation[5]];
    
    // Apply same offset and scale as image draw (pan/zoom handled by outer transform)
    let appliedDisplayTransform = false;
    if (displayParams) {
        const scaleX = displayParams.displayWidth / displayParams.dataWidth;
        const scaleY = displayParams.displayHeight / displayParams.dataHeight;
        ctx.save();
        ctx.translate(displayParams.offsetX || 0, displayParams.offsetY || 0);
        ctx.scale(scaleX, scaleY);
        appliedDisplayTransform = true;
    }
    
    const previewSettings = getLivePreviewSettings();

    // Draw each ROI contour
    RTSSMarks.forEach((mark) => {
        // Check if this contour belongs to the current slice
        if ((mark.sop || mark.sopInstanceUID) !== sopUID) return;
        
        // Check if the ROI is visible by name
        const roi = roiData.find(r => r.name === mark.showName || r.name === mark.hideName);
        if (!roi || !roi.visible) return;
        
        // Parse contour points
        const points = mark.pointArray;
        if (!points || points.length === 0) return;
        
        ctx.save();

        const previewActive = !!(previewSettings && roi.selected);

        ctx.beginPath();
        const polygon = [];
        for (let i = 0; i < points.length; i++) {
            const x = points[i].x;
            const y = points[i].y;
            const dx = x - imgPos[0];
            const dy = y - imgPos[1];
            const pixelX = (dx * rowCosines[0] + dy * colCosines[0]) / pixSpacing[0];
            const pixelY = (dx * rowCosines[1] + dy * colCosines[1]) / pixSpacing[1];
            polygon.push([pixelX, pixelY]);
            if (i === 0) ctx.moveTo(pixelX, pixelY);
            else ctx.lineTo(pixelX, pixelY);
        }

        if (polygon.length > 2) ctx.closePath();

        const doFillValidation = window.showBurnValidation && window.lastBurnNames && window.lastBurnNames.includes(roi.name);
        const doPreviewFill = previewActive && previewSettings.fillEnabled;
        if (doFillValidation || doPreviewFill) {
            ctx.save();
            ctx.fillStyle = doFillValidation ? (roi.color || '#ffff00') : 'rgba(255,255,0,0.18)';
            ctx.globalAlpha = doFillValidation ? 0.5 : 1;
            ctx.fill();
            ctx.restore();
        }

        if (previewActive) {
            const lwBase = previewSettings.lineWidth || 2;
            const overrideWidth = parseFloat(roi.lineWidthOverride);
            const effectiveWidth = Number.isFinite(overrideWidth) && overrideWidth > 0 ? overrideWidth : lwBase;
            const style = (roi.lineStyleOverride && roi.lineStyleOverride !== 'global')
                ? roi.lineStyleOverride
                : (previewSettings.lineStyle || 'solid');
            ctx.strokeStyle = '#ffff00';
            ctx.lineWidth = effectiveWidth;
            ctx.globalAlpha = 0.95;
            if (style === 'dotted') {
                const gap = Math.max(4, effectiveWidth * 2.5);
                ctx.setLineDash([effectiveWidth, gap]);
            } else ctx.setLineDash([]);
        } else {
            ctx.strokeStyle = roi.color || mark.color || '#00ff00';
            const overrideWidth = parseFloat(roi.lineWidthOverride);
            const fallbackWidth = Number.isFinite(overrideWidth) && overrideWidth > 0 ? overrideWidth : 2;
            ctx.lineWidth = fallbackWidth;
            ctx.globalAlpha = 0.8;
            ctx.setLineDash([]);
        }

        if (!doFillValidation || previewActive) {
            ctx.lineJoin = 'round';
            ctx.lineCap = 'round';
            ctx.stroke();
        }

        ctx.restore();
    });

    if (appliedDisplayTransform) {
        ctx.restore();
    }
}

// Crosshair helpers
function withDisplayTransform(ctx, displayParams, drawFn) {
    if (!displayParams) { drawFn(); return; }
    const scaleX = displayParams.displayWidth / displayParams.dataWidth;
    const scaleY = displayParams.displayHeight / displayParams.dataHeight;
    ctx.save();
    ctx.translate(displayParams.offsetX || 0, displayParams.offsetY || 0);
    ctx.scale(scaleX, scaleY);
    drawFn();
    ctx.restore();
}

function drawCrosshairAxial(ctx, displayParams, width, height) {
    const xIndex = viewportState.sagittal.currentSliceX || 0; // columns
    const yIndex = viewportState.coronal.currentSliceY || 0;  // rows
    withDisplayTransform(ctx, displayParams, () => {
        ctx.save();
        ctx.lineWidth = 1.5;
        ctx.setLineDash([]);
        ctx.strokeStyle = 'rgba(236,102,2,0.6)';
        ctx.beginPath();
        ctx.moveTo(xIndex + 0.5, 0);
        ctx.lineTo(xIndex + 0.5, height);
        ctx.stroke();
        // Horizontal line (coronal position)
        ctx.beginPath();
        ctx.moveTo(0, yIndex + 0.5);
        ctx.lineTo(width, yIndex + 0.5);
        ctx.stroke();
        ctx.restore();
    });
}

function drawCrosshairSagittal(ctx, displayParams, volume) {
    const width = volume.height;  // Y
    const height = volume.depth;  // Z
    const yIndex = viewportState.coronal.currentSliceY || 0;
    const zIndex = window.simpleViewerData.currentSlice || 0;
    withDisplayTransform(ctx, displayParams, () => {
        ctx.save();
        ctx.lineWidth = 1.5;
        ctx.setLineDash([]);
        ctx.strokeStyle = 'rgba(236,102,2,0.6)';
        // Vertical line at Y (coronal)
        ctx.beginPath();
        ctx.moveTo(yIndex + 0.5, 0);
        ctx.lineTo(yIndex + 0.5, height);
        ctx.stroke();
        // Horizontal line at Z (axial)
        ctx.beginPath();
        ctx.moveTo(0, (height - 1 - zIndex) + 0.5);
        ctx.lineTo(width, (height - 1 - zIndex) + 0.5);
        ctx.stroke();
        ctx.restore();
    });
}

function drawCrosshairCoronal(ctx, displayParams, volume) {
    const width = volume.width;   // X
    const height = volume.depth;  // Z
    const xIndex = viewportState.sagittal.currentSliceX || 0;
    const zIndex = window.simpleViewerData.currentSlice || 0;
    withDisplayTransform(ctx, displayParams, () => {
        ctx.save();
        ctx.lineWidth = 1.5;
        ctx.setLineDash([]);
        ctx.strokeStyle = 'rgba(236,102,2,0.6)';
        // Vertical line at X (sagittal)
        ctx.beginPath();
        ctx.moveTo(xIndex + 0.5, 0);
        ctx.lineTo(xIndex + 0.5, height);
        ctx.stroke();
        // Horizontal line at Z (axial)
        ctx.beginPath();
        ctx.moveTo(0, (height - 1 - zIndex) + 0.5);
        ctx.lineTo(width, (height - 1 - zIndex) + 0.5);
        ctx.stroke();
        ctx.restore();
    });
}

// Center crosshair at mouse position across views
function centerCrosshairAt(viewName, evt) {
    updateCrosshairFromMouse(viewName, evt, true);
}

function updateCrosshairFromMouse(viewName, evt, centerOnly = false) {
    if (!window.viewGeom) return;
    const canvas = document.getElementById(`viewport-${viewName}`);
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const sx = evt.clientX - rect.left;
    const sy = evt.clientY - rect.top;

    const geom = window.viewGeom[viewName];
    const state = viewportState[viewName];
    if (!geom || !state) return;
    const cx = geom.canvasWidth / 2;
    const cy = geom.canvasHeight / 2;

    // Undo pan/zoom
    const bx = (sx - cx - geom.panX) / geom.zoom + cx;
    const by = (sy - cy - geom.panY) / geom.zoom + cy;
    // Into image data coords
    const scaleX = geom.displayWidth / geom.dataWidth;
    const scaleY = geom.displayHeight / geom.dataHeight;
    const dx = (bx - geom.offsetX) / scaleX;
    const dy = (by - geom.offsetY) / scaleY;

    if (viewName === 'axial') {
        // dx -> X (sagittal), dy -> Y (coronal)
        viewportState.sagittal.currentSliceX = clampIndex(Math.round(dx), 0, geom.dataWidth - 1);
        viewportState.coronal.currentSliceY = clampIndex(Math.round(dy), 0, geom.dataHeight - 1);
    } else if (viewName === 'sagittal') {
        const volume = window.volumeData;
        if (!volume) return;
        // Sagittal data coords: width=Y, height=Z (flipped vertical)
        const y = clampIndex(Math.round(dx), 0, volume.height - 1);
        const z = clampIndex(Math.round(volume.depth - 1 - dy), 0, volume.depth - 1);
        viewportState.coronal.currentSliceY = y;
        if (window.simpleViewerData) window.simpleViewerData.currentSlice = z;
    } else if (viewName === 'coronal') {
        const volume = window.volumeData;
        if (!volume) return;
        const x = clampIndex(Math.round(dx), 0, volume.width - 1);
        const z = clampIndex(Math.round(volume.depth - 1 - dy), 0, volume.depth - 1);
        viewportState.sagittal.currentSliceX = x;
        if (window.simpleViewerData) window.simpleViewerData.currentSlice = z;
    }
    displaySimpleViewer();
}

function clampIndex(v, min, max) { return Math.max(min, Math.min(max, v)); }

// Draw ROI overlay on sagittal view
// (Removed duplicate stub: drawROIOverlaySagittal without displayParams)

// Draw ROI overlay on coronal view
// (Removed duplicate stub: drawROIOverlayCoronal without displayParams)

// RTSTRUCT parsing (replaces BlueLight helpers)
function getROINameList(dataSet) {
    const out = [];
    const seq = dataSet?.elements?.x30060020?.items || [];
    for (const it of seq) {
        const ds = it.dataSet;
        if (!ds) continue;
        const name = ds.string?.(Tag.ROIName) || ds.string?.('x30060026');
        if (name) out.push(String(name));
    }
    return out;
}

function readDicomRTSS(dataSet) {
    // Clear and repopulate RTSSMarks
    RTSSMarks.length = 0;
    try {
        // Build ROINumber -> Name map from StructureSetROISequence
        const roiNumToName = {};
        const ssItems = dataSet?.elements?.x30060020?.items || [];
        for (const it of ssItems) {
            const ds = it.dataSet;
            if (!ds) continue;
            const num = ds.intString?.(Tag.ROINumber) || ds.uint16?.(Tag.ROINumber) || parseInt(ds.string?.(Tag.ROINumber) || '');
            const name = ds.string?.(Tag.ROIName) || '';
            if (!isNaN(num)) roiNumToName[num] = name;
        }

        // Build ROINumber -> color from ROIContourSequence
        const roiNumToColor = {};
        const rcItems = dataSet?.elements?.x30060039?.items || [];
        for (const it of rcItems) {
            const ds = it.dataSet;
            if (!ds) continue;
            const num = ds.intString?.(Tag.ReferencedROINumber) || ds.uint16?.(Tag.ReferencedROINumber) || parseInt(ds.string?.(Tag.ReferencedROINumber) || '');
            const colorStr = ds.string?.(Tag.ROIDisplayColor) || '';
            if (colorStr) {
                const [r,g,b] = String(colorStr).split('\\').map(v=>parseInt(v));
                roiNumToColor[num] = `rgb(${r}, ${g}, ${b})`;
            }
            const cseq = ds.elements?.x30060040?.items || [];
            for (const c of cseq) {
                const cds = c.dataSet; if (!cds) continue;
                // Find referenced SOP for this contour
                let sop = null;
                try {
                    sop = cds.elements?.x30060016?.items?.[0]?.dataSet?.string?.(Tag.ReferencedSOPInstanceUID)
                       || cds.elements?.x30060016?.items?.[0]?.dataSet?.string?.('x00081155')
                       || cds.string?.(Tag.ReferencedSOPInstanceUID);
                } catch {}
                const contourData = cds.string?.(Tag.ContourData) || '';
                if (!contourData) continue;
                const vals = String(contourData).split('\\').map(parseFloat).filter(v=>!isNaN(v));
                const pts = [];
                for (let i = 0; i + 2 < vals.length; i += 3) {
                    pts.push({ x: vals[i], y: vals[i+1], z: vals[i+2] });
                }
                const name = roiNumToName[num] || `ROI ${num}`;
                const color = roiNumToColor[num];
                if (pts.length) {
                    RTSSMarks.push({ sop, showName: name, hideName: name, color, type: 'RTSS', pointArray: pts });
                }
            }
        }
        // No-op refresh hook compatibility
        try { refreshMarkFromSeries(); } catch {}
    } catch (e) {
        console.warn('Failed to parse RTSTRUCT:', e);
    }
}

function addSelectedROIs() {
    const selectedItems = document.querySelectorAll('.roi-item.selected');
    const tbody = document.getElementById('roiTableBody');
    
    selectedItems.forEach(item => {
        const roiName = item.textContent.replace('✓', '').trim();
        const roiNumber = item.dataset.roiNumber;
        
        // Check if already added
        if (roiSettings.find(r => r.name === roiName)) {
            return;
        }
        
        const row = tbody.insertRow();
        const rowId = `roi_row_${roiNumber}`;
        row.id = rowId;
        
        // ROI Name
        row.insertCell(0).textContent = roiName;
        
        // Contour checkbox
        const contourCell = row.insertCell(1);
        contourCell.className = 'checkbox-cell';
        contourCell.innerHTML = '<input type="checkbox" class="custom-checkbox contour-check">';
        
        // Fill checkbox
        const fillCell = row.insertCell(2);
        fillCell.className = 'checkbox-cell';
        fillCell.innerHTML = '<input type="checkbox" class="custom-checkbox fill-check">';
        
        // Preset dropdown
        const presetCell = row.insertCell(3);
        const presetSelect = document.createElement('select');
        presetSelect.className = 'preset-select';
        Object.keys(HU_PRESETS).forEach(preset => {
            const option = document.createElement('option');
            option.value = preset;
            option.textContent = preset;
            presetSelect.appendChild(option);
        });
        presetSelect.value = 'Water (0 HU)';
        presetCell.appendChild(presetSelect);
        
        // Manual HU input
        const manualCell = row.insertCell(4);
        const manualInput = document.createElement('input');
        manualInput.type = 'number';
        manualInput.className = 'manual-input';
        manualInput.disabled = true;
        manualInput.placeholder = 'HU';
        manualCell.appendChild(manualInput);
        
        // Remove button
        const actionCell = row.insertCell(5);
        const removeBtn = document.createElement('button');
        removeBtn.className = 'remove-btn';
        removeBtn.textContent = 'Remove';
        removeBtn.onclick = function() {
            roiSettings = roiSettings.filter(r => r.name !== roiName);
            row.remove();
        };
        actionCell.appendChild(removeBtn);
        
        // Handle preset change
        presetSelect.addEventListener('change', function() {
            if (this.value === 'Manual Entry') {
                manualInput.disabled = false;
                manualInput.value = '0';
            } else {
                manualInput.disabled = true;
                manualInput.value = '';
            }
        });
        
        // Handle checkbox exclusivity
        const contourCheck = row.querySelector('.contour-check');
        const fillCheck = row.querySelector('.fill-check');
        
        contourCheck.addEventListener('change', function() {
            if (this.checked) fillCheck.checked = false;
        });
        
        fillCheck.addEventListener('change', function() {
            if (this.checked) contourCheck.checked = false;
        });
        
        // Add to settings
        roiSettings.push({
            name: roiName,
            number: roiNumber,
            row: row
        });
        
        // Clear selection
        item.classList.remove('selected');
    });
    
    // Set default image set name if first ROI
    if (roiSettings.length === 1 && !document.getElementById('imageSetName').value) {
        document.getElementById('imageSetName').value = roiSettings[0].name;
    }
}

// Geometry helpers
function densifyContour(points, maxMm = 1.0) {
    const output = [];
    for (let i = 0; i < points.length; i++) {
        const p0 = points[i];
        const p1 = points[(i + 1) % points.length];
        
        const dx = p1[0] - p0[0];
        const dy = p1[1] - p0[1];
        const dz = p1[2] - p0[2];
        const segmentLength = Math.sqrt(dx*dx + dy*dy + dz*dz);
        
        const steps = Math.max(Math.ceil(segmentLength / maxMm), 1);
        
        for (let k = 0; k < steps; k++) {
            const t = k / steps;
            output.push([
                p0[0] + dx * t,
                p0[1] + dy * t,
                p0[2] + dz * t
            ]);
        }
    }
    return output;
}

function worldToPixel(worldPoint, imagePosition, pixelSpacing) {
    const x = Math.round((worldPoint[0] - imagePosition[0]) / pixelSpacing[0]);
    const y = Math.round((worldPoint[1] - imagePosition[1]) / pixelSpacing[1]);
    return [x, y];
}

function fillPolygon(imageData, polygon, value, width, height) {
    // Create a canvas for polygon filling
    const canvas = document.getElementById('canvasContainer');
    canvas.width = width;
    canvas.height = height;
    const ctx = canvas.getContext('2d');
    
    // Clear canvas
    ctx.clearRect(0, 0, width, height);
    
    // Draw polygon
    ctx.beginPath();
    ctx.moveTo(polygon[0][0], polygon[0][1]);
    for (let i = 1; i < polygon.length; i++) {
        ctx.lineTo(polygon[i][0], polygon[i][1]);
    }
    ctx.closePath();
    ctx.fillStyle = 'white';
    ctx.fill();
    
    // Get mask data
    const maskData = ctx.getImageData(0, 0, width, height);
    
    // Apply mask to image data
    for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
            const idx = (y * width + x) * 4;
            if (maskData.data[idx] > 0) {
                imageData[y * width + x] = value;
            }
        }
    }
}

function drawContour(imageData, polygon, value, width, height) {
    // Draw contour points
    for (const point of polygon) {
        const x = point[0];
        const y = point[1];
        if (x >= 0 && x < width && y >= 0 && y < height) {
            imageData[y * width + x] = value;
        }
    }
}

// Stamp HU around a point with given line width (exact NxN brush in image pixels)
function stampHU(huData, width, height, x, y, huValue, lineWidth) {
    const w = Math.max(1, Math.round(lineWidth || 1));
    if (w === 1) {
        if (x >= 0 && x < width && y >= 0 && y < height) huData[y * width + x] = huValue;
        return;
    }
    const even = (w % 2 === 0);
    const half = Math.floor(w / 2);
    let xStart, xEnd, yStart, yEnd;
    if (even) {
        xStart = x;
        xEnd = x + (w - 1);
        yStart = y;
        yEnd = y + (w - 1);
    } else {
        xStart = x - half;
        xEnd = x + half;
        yStart = y - half;
        yEnd = y + half;
    }
    xStart = Math.max(0, xStart);
    yStart = Math.max(0, yStart);
    xEnd = Math.min(width - 1, xEnd);
    yEnd = Math.min(height - 1, yEnd);
    for (let yy = yStart; yy <= yEnd; yy++) {
        const rowBase = yy * width;
        for (let xx = xStart; xx <= xEnd; xx++) huData[rowBase + xx] = huValue;
    }
}

function applyFillHUFromPolygons(huData, baselineHU, width, height, polygons, deltaHU) {
    if (!polygons || polygons.length === 0) return;
    if (!Number.isFinite(deltaHU)) return;

    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    polygons.forEach(poly => {
        poly.forEach(([x, y]) => {
            if (x < minX) minX = x;
            if (x > maxX) maxX = x;
            if (y < minY) minY = y;
            if (y > maxY) maxY = y;
        });
    });

    if (!Number.isFinite(minX) || !Number.isFinite(minY) || !Number.isFinite(maxX) || !Number.isFinite(maxY)) return;

    const margin = 2;
    const minXFloor = Math.max(0, Math.floor(minX) - margin);
    const minYFloor = Math.max(0, Math.floor(minY) - margin);
    const maxXCeil = Math.min(width - 1, Math.ceil(maxX) + margin);
    const maxYCeil = Math.min(height - 1, Math.ceil(maxY) + margin);
    const bboxW = maxXCeil - minXFloor + 1;
    const bboxH = maxYCeil - minYFloor + 1;
    if (bboxW <= 0 || bboxH <= 0) return;

    const canvas = document.createElement('canvas');
    canvas.width = bboxW;
    canvas.height = bboxH;
    const ctx = canvas.getContext('2d');
    if (!ctx) return;
    ctx.clearRect(0, 0, bboxW, bboxH);
    ctx.save();
    ctx.translate(-minXFloor, -minYFloor);
    ctx.fillStyle = '#ffffff';
    ctx.beginPath();
    polygons.forEach(poly => {
        if (!poly || poly.length < 3) return;
        ctx.moveTo(poly[0][0], poly[0][1]);
        for (let i = 1; i < poly.length; i++) ctx.lineTo(poly[i][0], poly[i][1]);
        ctx.closePath();
    });
    ctx.fill('evenodd');
    ctx.restore();

    const imageData = ctx.getImageData(0, 0, bboxW, bboxH);
    const data = imageData.data;
    const clampHU = (val) => Math.max(-1024, Math.min(12000, val));
    const safeDelta = Math.max(-5000, Math.min(5000, deltaHU));

    for (let y = 0; y < bboxH; y++) {
        const py = minYFloor + y;
        if (py < 0 || py >= height) continue;
        const rowBase = py * width;
        for (let x = 0; x < bboxW; x++) {
            const px = minXFloor + x;
            if (px < 0 || px >= width) continue;
            const alpha = data[(y * bboxW + x) * 4 + 3];
            if (alpha < 128) continue;
            const idx = rowBase + px;
            const sourceValue = baselineHU ? baselineHU[idx] : huData[idx];
            huData[idx] = clampHU(sourceValue + safeDelta);
        }
    }
}

function stampFooterAnnotation(huData, width, height, roiEntries, delta = FOOTER_DELTA_HU, noteText = '') {
    if (!roiEntries || roiEntries.length === 0) return;
    // Build footer lines:
    // 0..n) Optional note (up to 5 lines)
    // last-1) "Name, Line Style[, +/-HU overlay] | ..."
    // last) "NOT FOR DOSE CALCULATION"
    const line1 = roiEntries.map(entry => {
        const name = entry?.name || 'ROI';
        const styleStr = (String(entry?.lineStyle).toLowerCase() === 'dotted') ? 'Dotted' : 'Solid';
        const d = entry?.deltaHU;
        let overlay = '';
        if (Number.isFinite(d) && d !== 0) {
            overlay = `, ${d > 0 ? '+' : ''}${Math.round(d)} HU overlay`;
        }
        return `${name}, ${styleStr}${overlay}`;
    }).join(' | ');
    const line2 = 'NOT FOR DOSE CALCULATION';

    const canvas = document.createElement('canvas');
    canvas.width = width;
    // Prepare a measuring context first (height may change later and reset state)
    let mctx = canvas.getContext('2d');
    if (!mctx) return;
    mctx.font = `${FOOTER_FONT_PX}px sans-serif`;
    // Wrap note up to 5 lines across full width
    const margin = 0; // full width
    const hasNote = !!noteText && String(noteText).trim().length > 0;
    let noteLines = [];
    if (hasNote) {
        const maxLines = 5;
        const words = String(noteText).trim().split(/\s+/);
        let current = '';
        for (const w of words) {
            const test = current ? current + ' ' + w : w;
            const m = mctx.measureText(test);
            if (m.width <= (width - margin * 2) || current.length === 0) {
                current = test;
            } else {
                noteLines.push(current);
                current = w;
                if (noteLines.length >= maxLines - 1) break;
            }
        }
        if (noteLines.length < maxLines && current) noteLines.push(current);
        if (noteLines.length > maxLines) noteLines = noteLines.slice(0, maxLines);
        // Ellipsis if overflow
        if (noteLines.length === maxLines) {
            const last = noteLines[maxLines - 1];
            let trimmed = last;
            while (mctx.measureText(trimmed + '…').width > (width - margin * 2) && trimmed.length > 0) {
                trimmed = trimmed.slice(0, -1);
            }
            noteLines[maxLines - 1] = trimmed + (trimmed === last ? '' : '…');
        }
    }
    const linesCount = 2 + noteLines.length;
    const lineGap = Math.max(2, Math.round(FOOTER_FONT_PX * 0.3));
    canvas.height = linesCount * FOOTER_FONT_PX + lineGap * (linesCount + 1);
    const ctx = canvas.getContext('2d');
    if (!ctx) return;
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.font = `${FOOTER_FONT_PX}px sans-serif`;
    ctx.fillStyle = '#ffffff';
    ctx.textBaseline = 'top';
    ctx.textAlign = 'left';
    let drawY = lineGap;
    for (const ln of noteLines) {
        ctx.fillText(ln, margin, drawY);
        drawY += FOOTER_FONT_PX + lineGap;
    }
    ctx.fillText(line1, margin, drawY);
    drawY += FOOTER_FONT_PX + lineGap;
    ctx.fillText(line2, margin, drawY);

    const img = ctx.getImageData(0, 0, canvas.width, canvas.height);
    const data = img.data;
    const startRow = height - canvas.height;
    const clampHU = (val) => Math.max(-1024, Math.min(12000, val));
    for (let y = 0; y < canvas.height; y++) {
        const py = startRow + y;
        if (py < 0 || py >= height) continue;
        const rowBase = py * width;
        for (let x = 0; x < canvas.width; x++) {
            const alpha = data[(y * canvas.width + x) * 4 + 3];
            if (alpha < 128) continue;
            const idx = rowBase + x;
            huData[idx] = clampHU(FOOTER_TEXT_HU);
        }
    }
}

// Hard-burn a warning label at the top-left corner on every slice (or bottom if requested)
function stampTopLeftWarning(huData, width, height, text = 'NOT VALIDATED FOR CLINICAL USE', topOffset = null, placeBottom = false) {
    if (!text || !text.trim()) return;

    // Prepare a measuring canvas to size the final draw
    const measureCanvas = document.createElement('canvas');
    const mctx = measureCanvas.getContext('2d');
    if (!mctx) return;
    mctx.font = `${FOOTER_FONT_PX}px sans-serif`;
    const margin = Math.max(FOOTER_MARGIN, 4);
    const metrics = mctx.measureText(text);
    // Ensure we do not exceed the image width
    const canvasWidth = Math.min(width, Math.ceil(metrics.width) + margin * 2);
    const canvasHeight = FOOTER_FONT_PX + margin * 2;

    const canvas = document.createElement('canvas');
    canvas.width = canvasWidth;
    canvas.height = canvasHeight;
    const ctx = canvas.getContext('2d');
    if (!ctx) return;
    ctx.clearRect(0, 0, canvasWidth, canvasHeight);
    ctx.font = `${FOOTER_FONT_PX}px sans-serif`;
    ctx.fillStyle = '#ffffff';
    ctx.textBaseline = 'top';
    ctx.textAlign = 'left';
    ctx.fillText(text, margin, margin);

    const img = ctx.getImageData(0, 0, canvasWidth, canvasHeight);
    const data = img.data;
    const clampHU = (val) => Math.max(-1024, Math.min(12000, val));
    const startRow = placeBottom
        ? Math.max(0, height - canvasHeight - margin)
        : ((topOffset !== null && Number.isFinite(topOffset)) ? topOffset : 0);
    for (let y = 0; y < canvasHeight; y++) {
        const py = startRow + y;
        if (py < 0 || py >= height) continue;
        const rowBase = py * width;
        for (let x = 0; x < canvasWidth; x++) {
            const alpha = data[(y * canvasWidth + x) * 4 + 3];
            if (alpha < 128) continue;
            const idx = rowBase + x;
            huData[idx] = clampHU(FOOTER_TEXT_HU);
        }
    }
}

function burnSlices(sourceSlices, burnInSettings, options = {}) {
    if (!sourceSlices || sourceSlices.length === 0) return [];
    if (!burnInSettings || burnInSettings.length === 0) return sourceSlices.map(slice => ({ ...slice }));

    const {
        textEnabled = false,
        textInterval = 5,
        textDeltaHU = 100,
        textFontPx = ptToPx(TEXT_FONT_PT_DEFAULT),
        footerDelta = FOOTER_DELTA_HU,
        progressCallback = null
    } = options;

    const totalSlices = sourceSlices.length;
    const anyFillEnabled = burnInSettings.some(s => s.fill && Number.isFinite(s.fillDeltaHU));
    const processed = [];

    for (let sliceIdx = 0; sliceIdx < totalSlices; sliceIdx++) {
        const ctFile = sourceSlices[sliceIdx];
        const dataSet = ctFile?.dataSet;
        if (!dataSet || !dataSet.elements?.x7fe00010) {
            processed.push(ctFile);
            if (progressCallback) {
                try { progressCallback(sliceIdx + 1, totalSlices); } catch (err) { console.debug('burnSlices progress callback error:', err); }
            }
            continue;
        }

        const width = dataSet.uint16(Tag.Columns) || 512;
        const height = dataSet.uint16(Tag.Rows) || 512;
        const pixelSpacing = (dataSet.string(Tag.PixelSpacing) || '1\\1').split('\\').map(parseFloat);
        const pixelDataElement = dataSet.elements.x7fe00010;
        const offset = pixelDataElement.dataOffset;
        const length = pixelDataElement.length;

        let pixelData = ctFile.modifiedPixelData;
        if (!pixelData) {
            try {
                if (ctFile.byteArray) pixelData = new Int16Array(ctFile.byteArray.buffer, offset, length / 2);
                else if (dataSet.byteArray) pixelData = new Int16Array(dataSet.byteArray.buffer, offset, length / 2);
            } catch (err) {
                console.error('burnSlices: failed to access pixel data', err);
            }
        }
        if (!pixelData) {
            processed.push(ctFile);
            if (progressCallback) {
                try { progressCallback(sliceIdx + 1, totalSlices); } catch (err) { console.debug('burnSlices progress callback error:', err); }
            }
            continue;
        }

        const slope = dataSet.floatString(Tag.RescaleSlope) || 1;
        const intercept = dataSet.floatString(Tag.RescaleIntercept) || 0;
        const huData = new Float32Array(pixelData.length);
        for (let i = 0; i < pixelData.length; i++) {
            huData[i] = pixelData[i] * slope + intercept;
        }

        const baselineHU = anyFillEnabled ? Float32Array.from(huData) : null;
        const imagePosition = (dataSet.string(Tag.ImagePositionPatient) || '0\\0\\0').split('\\').map(parseFloat);
        const imageOrientation = (dataSet.string(Tag.ImageOrientationPatient) || '1\\0\\0\\0\\1\\0').split('\\').map(parseFloat);
        const rowCos = [imageOrientation[0], imageOrientation[1], imageOrientation[2]];
        const colCos = [imageOrientation[3], imageOrientation[4], imageOrientation[5]];
        const sopUID = dataSet.string(Tag.SOPInstanceUID);

        const roiPolysForSlice = new Map();
        const contourSegments = new Map();

        burnInSettings.forEach(setting => {
            (RTSSMarks || []).forEach(mark => {
                if ((mark.sop || mark.sopInstanceUID) !== sopUID) return;
                if (!(mark.showName === setting.name || mark.hideName === setting.name)) return;
                if (!mark.pointArray || mark.pointArray.length === 0) return;

                const points3D = mark.pointArray.map(p => [p.x, p.y, p.z]);
                const polygon = points3D.map(pt => {
                    const dx = pt[0] - imagePosition[0];
                    const dy = pt[1] - imagePosition[1];
                    const px = (dx * rowCos[0] + dy * colCos[0]) / (pixelSpacing[0] || 1);
                    const py = (dx * rowCos[1] + dy * colCos[1]) / (pixelSpacing[1] || 1);
                    return [px, py];
                });
                if (polygon.length < 3) return;

                if (!roiPolysForSlice.has(setting.name)) roiPolysForSlice.set(setting.name, []);
                roiPolysForSlice.get(setting.name).push(polygon);

                if (setting.contour) {
                    const densePoints = densifyContour(points3D, 1.0);
                    const pixelPoints = densePoints.map(point => {
                        const dx = point[0] - imagePosition[0];
                        const dy = point[1] - imagePosition[1];
                        const px = (dx * rowCos[0] + dy * colCos[0]) / (pixelSpacing[0] || 1);
                        const py = (dx * rowCos[1] + dy * colCos[1]) / (pixelSpacing[1] || 1);
                        return [Math.round(px), Math.round(py)];
                    });
                    if (!contourSegments.has(setting.name)) contourSegments.set(setting.name, []);
                    contourSegments.get(setting.name).push({
                        points: pixelPoints,
                        lineStyle: setting.lineStyle,
                        lineWidth: setting.lineWidth,
                        huValue: setting.huValue
                    });
                }
            });
        });

        if (anyFillEnabled) {
            burnInSettings.forEach(setting => {
                if (!setting.fill) return;
                if (!Number.isFinite(setting.fillDeltaHU)) return;
                const polys = roiPolysForSlice.get(setting.name);
                if (polys && polys.length) {
                    applyFillHUFromPolygons(huData, baselineHU || huData, width, height, polys, setting.fillDeltaHU);
                }
            });
        }

        contourSegments.forEach((segments) => {
            segments.forEach(segment => {
                const patternStep = segment.lineStyle === 'dotted' ? 6 : 1; // align with external fixed pattern
                for (let i = 0; i < segment.points.length; i++) {
                    if (segment.lineStyle === 'dotted' && (i % patternStep) !== 0) continue;
                    const [x, y] = segment.points[i];
                    stampHU(huData, width, height, x, y, segment.huValue, segment.lineWidth || 2);
                }
            });
        });

        if (footerDelta) {
            const footerEntries = burnInSettings.map(s => ({
                name: s.name,
                lineStyle: s.lineStyle,
                deltaHU: (s.fill && Number.isFinite(s.fillDeltaHU)) ? s.fillDeltaHU : null
            }));
            const noteText = options && typeof options.noteText === 'string' ? options.noteText : '';
            stampFooterAnnotation(huData, width, height, footerEntries, footerDelta, noteText);
        }

        // Always stamp warnings and provenance on MR padded output
        if (options?.mrContext) {
            const { ctSeriesName, mrSeriesName } = options.mrContext;
            stampTopLeftWarning(huData, width, height, 'NOT FOR DOSE CALCULATION');
            if (ctSeriesName || mrSeriesName) {
                const lines = [
                    ctSeriesName ? `CT: ${ctSeriesName}` : '',
                    mrSeriesName ? `MR: ${mrSeriesName}` : ''
                ].filter(Boolean);
                lines.forEach((line, idx) => {
                    const margin = FOOTER_MARGIN + idx * (FOOTER_FONT_PX + 4);
                    stampTopLeftWarning(huData, width, height, line, margin);
                });
            }
            stampTopLeftWarning(huData, width, height, 'NOT FOR CLINICAL USE', null, true);
        } else {
            // Legacy warning for RT burn flows
            stampTopLeftWarning(huData, width, height, 'NOT VALIDATED FOR CLINICAL USE');
        }

        // TODO: textEnabled support for future enhancement
        if (textEnabled && sliceIdx % Math.max(1, textInterval) === 0) {
            // Placeholder for future text stamping logic
        }

        const modifiedPixelData = new Int16Array(huData.length);
        for (let i = 0; i < huData.length; i++) {
            const rawValue = Math.round((huData[i] - intercept) / slope);
            modifiedPixelData[i] = Math.max(-32768, Math.min(32767, rawValue));
        }

        processed.push({ ...ctFile, modifiedPixelData, huData });

        if (progressCallback) {
            try { progressCallback(sliceIdx + 1, totalSlices); } catch (err) { console.debug('burnSlices progress callback error:', err); }
        }
    }

    return processed;
}

// Store original CT data for viewer
let originalCTData = [];
let processedCTData = [];
let dicomViewer = null;

async function burnInROIs() {
    const config = collectBurnConfig();
    if (!config) return;

    if (window.previewMode) {
        clearPreview();
    }

    const { burnInSettings, burnNames, separateSeries } = config;
    updateStatus('Processing burn-in...');
    updateProgress(0);

    originalCTData = [...ctFiles];

    const burnOptions = {
        textEnabled: false,
        textInterval: 1,
        textDeltaHU: 100,
        textFontPx: ptToPx(TEXT_FONT_PT_DEFAULT),
        footerDelta: FOOTER_DELTA_HU,
        noteText: config.noteText,
        progressCallback: (current, total) => updateProgress((current / total) * 100)
    };

    if (separateSeries) {
        const seriesList = [];
        for (const setting of burnInSettings) {
            const processed = burnSlices(ctFiles, [setting], burnOptions);
            seriesList.push({ processedCTs: processed, roiName: setting.name, hu: setting.huValue });
        }
        await exportMultipleSeriesToOneZip(seriesList);
        showMessage('success', `Exported ${burnInSettings.length} burned series (one ZIP, subfolders per ROI).`);
        updateStatus('Export complete');
        return;
    }

    processedCTData = burnSlices(ctFiles, burnInSettings, burnOptions);

    window.tempExportPairs = burnInSettings.map(s => `${s.name}_${s.huValue}HU`);
    await exportModifiedDICOM(processedCTData);
    window.tempExportPairs = undefined;

    ctFiles = processedCTData;
    if (window.simpleViewerData) window.simpleViewerData.isShowingBurned = true;
    window.showBurnValidation = true;
    window.lastBurnNames = burnNames;
    window.volumeData = null;

    displaySimpleViewer();

    updateStatus('Burn-in complete!');
    showMessage('success', 'ROIs have been burned into the images and exported.');
}

// Densify contour - insert points so edges are ≤ max_mm apart (matches Python)
function densifyContour(points, maxMM = 1.0) {
    const out = [];
    const numPoints = points.length;
    
    for (let i = 0; i < numPoints; i++) {
        const p0 = points[i];
        const p1 = points[(i + 1) % numPoints];
        
        // Calculate segment length
        const dx = p1[0] - p0[0];
        const dy = p1[1] - p0[1];
        const dz = p1[2] - p0[2];
        const segLen = Math.sqrt(dx*dx + dy*dy + dz*dz);
        
        // Calculate number of steps
        const steps = Math.max(Math.ceil(segLen / maxMM), 1);
        
        // Add interpolated points
        for (let k = 0; k < steps; k++) {
            const t = k / steps;
            out.push([
                p0[0] + dx * t,
                p0[1] + dy * t,
                p0[2] + dz * t
            ]);
        }
    }
    
    return out;
}

// Build or fetch cached 3D ROI mask
function getOrBuildROIMask(roiName, volume) {
    if (!volume || !volume.width) return null;
    if (roiMasks[roiName]) return roiMasks[roiName];

    const width = volume.width, height = volume.height, depth = volume.depth;
    const mask = new Uint8Array(width * height * depth);

    // Precompute mapping
    const rowSpacing = volume.pixelSpacing ? volume.pixelSpacing[0] : 1.0;
    const colSpacing = volume.pixelSpacing ? volume.pixelSpacing[1] : 1.0;

    // Collect marks for this ROI
    const marks = RTSSMarks.filter(m => m.type === 'RTSS' && (m.showName === roiName || m.hideName === roiName));
    if (!marks.length) return null;

    let minX = Infinity, minY = Infinity, minZ = Infinity;
    let maxX = -Infinity, maxY = -Infinity, maxZ = -Infinity;

    marks.forEach(mark => {
        const zIndex = volume.sopUIDIndex[(mark.sop || mark.sopInstanceUID)] ?? -1;
        if (zIndex < 0 || !mark.pointArray || mark.pointArray.length < 3) return;
        const firstPos = volume.imagePosition[zIndex];
        if (!firstPos) return;

        // Convert points to pixel coordinates for this slice
        const pts = mark.pointArray.map(p => [
            Math.round((p.x - firstPos[0]) / colSpacing),
            Math.round((p.y - firstPos[1]) / rowSpacing)
        ]);

        // Densify in mm space before pixels for smoother outlines
        const dense = densifyContour(mark.pointArray.map(p => [p.x, p.y, p.z]), 1.0).map(p => [
            Math.round((p[0] - firstPos[0]) / colSpacing),
            Math.round((p[1] - firstPos[1]) / rowSpacing)
        ]);

        rasterizePolygonToMask(mask, width, height, zIndex, dense);

        // Update bbox from original points (in patient mm converted to indices)
        for (const p of pts) {
            const x = p[0], y = p[1];
            if (x < minX) minX = x; if (x > maxX) maxX = x;
            if (y < minY) minY = y; if (y > maxY) maxY = y;
            if (zIndex < minZ) minZ = zIndex; if (zIndex > maxZ) maxZ = zIndex;
        }
    });

    const info = { mask, width, height, depth, bbox: { minX, minY, minZ, maxX, maxY, maxZ } };
    roiMasks[roiName] = info;
    return info;
}

// Marching squares for a sagittal slice (YZ plane) at x = sliceX
function getOrBuildContoursSag(roiName, sliceX, volume) {
    if (!roiContoursSag[roiName]) roiContoursSag[roiName] = new Map();
    const cache = roiContoursSag[roiName];
    if (cache.has(sliceX)) return cache.get(sliceX);
    const info = getOrBuildROIMask(roiName, volume);
    if (!info) return [];
    const { mask, width, height, depth } = info;
    const segments = [];
    // grid size: height (Y) x depth (Z)
    for (let z = 0; z < depth - 1; z++) {
        for (let y = 0; y < height - 1; y++) {
            const i00 = z * width * height + y * width + sliceX;
            const i10 = i00 + width; // y+1
            const i01 = i00 + width * height; // z+1
            const i11 = i01 + width; // y+1, z+1
            const v0 = mask[i00] ? 1 : 0;
            const v1 = mask[i10] ? 1 : 0;
            const v2 = mask[i11] ? 1 : 0;
            const v3 = mask[i01] ? 1 : 0;
            const code = (v0 << 0) | (v1 << 1) | (v2 << 2) | (v3 << 3);
            // edges: between cell corners: (y,z)
            const y0 = y, y1 = y + 1, z0 = z, z1 = z + 1;
            switch (code) {
                case 0: case 15: break;
                case 1: case 14: segments.push([y0, z0 + 0.5, y0 + 0.5, z0]); break;
                case 2: case 13: segments.push([y0 + 0.5, z0, y1, z0 + 0.5]); break;
                case 3: case 12: segments.push([y0, z0 + 0.5, y1, z0 + 0.5]); break;
                case 4: case 11: segments.push([y1, z0 + 0.5, y0 + 0.5, z1]); break;
                case 5: segments.push([y0, z0 + 0.5, y0 + 0.5, z0]); segments.push([y1, z0 + 0.5, y0 + 0.5, z1]); break;
                case 10: segments.push([y0 + 0.5, z0, y1, z0 + 0.5]); segments.push([y0, z0 + 0.5, y0 + 0.5, z1]); break;
                case 6: case 9: segments.push([y0 + 0.5, z0, y0 + 0.5, z1]); break;
                case 7: case 8: segments.push([y0, z0 + 0.5, y0 + 0.5, z1]); break;
            }
        }
    }
    cache.set(sliceX, segments);
    return segments;
}

// Marching squares for a coronal slice (XZ plane) at y = sliceY
function getOrBuildContoursCor(roiName, sliceY, volume) {
    if (!roiContoursCor[roiName]) roiContoursCor[roiName] = new Map();
    const cache = roiContoursCor[roiName];
    if (cache.has(sliceY)) return cache.get(sliceY);
    const info = getOrBuildROIMask(roiName, volume);
    if (!info) return [];
    const { mask, width, height, depth } = info;
    const segments = [];
    // grid size: width (X) x depth (Z)
    for (let z = 0; z < depth - 1; z++) {
        for (let x = 0; x < width - 1; x++) {
            const i00 = z * width * height + sliceY * width + x;
            const i10 = i00 + 1; // x+1
            const i01 = i00 + width * height; // z+1
            const i11 = i01 + 1; // x+1, z+1
            const v0 = mask[i00] ? 1 : 0;
            const v1 = mask[i10] ? 1 : 0;
            const v2 = mask[i11] ? 1 : 0;
            const v3 = mask[i01] ? 1 : 0;
            const code = (v0 << 0) | (v1 << 1) | (v2 << 2) | (v3 << 3);
            const x0 = x, x1 = x + 1, z0 = z, z1 = z + 1;
            switch (code) {
                case 0: case 15: break;
                case 1: case 14: segments.push([x0, z0 + 0.5, x0 + 0.5, z0]); break;
                case 2: case 13: segments.push([x0 + 0.5, z0, x1, z0 + 0.5]); break;
                case 3: case 12: segments.push([x0, z0 + 0.5, x1, z0 + 0.5]); break;
                case 4: case 11: segments.push([x1, z0 + 0.5, x0 + 0.5, z1]); break;
                case 5: segments.push([x0, z0 + 0.5, x0 + 0.5, z0]); segments.push([x1, z0 + 0.5, x0 + 0.5, z1]); break;
                case 10: segments.push([x0 + 0.5, z0, x1, z0 + 0.5]); segments.push([x0, z0 + 0.5, x0 + 0.5, z1]); break;
                case 6: case 9: segments.push([x0 + 0.5, z0, x0 + 0.5, z1]); break;
                case 7: case 8: segments.push([x0, z0 + 0.5, x0 + 0.5, z1]); break;
            }
        }
    }
    cache.set(sliceY, segments);
    return segments;
}

// Rasterize a polygon onto a z slice of mask (scanline fill)
function rasterizePolygonToMask(mask, width, height, zIndex, points) {
    if (!points || points.length < 3) return;
    // Clamp to bounds
    const minY = Math.max(0, Math.min(...points.map(p => p[1])));
    const maxY = Math.min(height - 1, Math.max(...points.map(p => p[1])));
    for (let y = minY; y <= maxY; y++) {
        const intersections = [];
        for (let i = 0, j = points.length - 1; i < points.length; j = i++) {
            const [x1, y1] = points[j];
            const [x2, y2] = points[i];
            if ((y1 > y) !== (y2 > y)) {
                const t = (y - y1) / (y2 - y1);
                const x = Math.round(x1 + t * (x2 - x1));
                intersections.push(x);
            }
        }
        intersections.sort((a, b) => a - b);
        for (let k = 0; k + 1 < intersections.length; k += 2) {
            const xStart = Math.max(0, intersections[k]);
            const xEnd = Math.min(width - 1, intersections[k + 1]);
            const base = zIndex * width * height + y * width;
            for (let x = xStart; x <= xEnd; x++) {
                mask[base + x] = 1;
            }
        }
    }
}

// Navigate to ROI center across three planes
async function goToROI(roiName) {
    let volume = window.volumeData;
    if (!volume) {
        volume = await createVolumeData();
        window.volumeData = volume;
        if (!volume) return;
    }
    const info = getOrBuildROIMask(roiName, volume);
    if (!info) return;
    const { bbox } = info;
    const centerX = Math.round((bbox.minX + bbox.maxX) / 2);
    const centerY = Math.round((bbox.minY + bbox.maxY) / 2);
    const centerZ = Math.round((bbox.minZ + bbox.maxZ) / 2);

    viewportState.sagittal.currentSliceX = Math.max(0, Math.min(volume.width - 1, centerX));
    viewportState.coronal.currentSliceY = Math.max(0, Math.min(volume.height - 1, centerY));
    if (window.simpleViewerData) {
        window.simpleViewerData.currentSlice = Math.max(0, Math.min(volume.depth - 1, centerZ));
    }
    displaySimpleViewer();
}

// Fill polygon using XOR for holes (matches Python implementation)
function fillPolygonXOR(huData, width, height, polygons, huValue) {
    // Create mask for XOR fill
    const mask = new Uint8Array(width * height);
    
    // Process each polygon with XOR
    polygons.forEach(points => {
        if (points.length < 3) return;
        
        const tempMask = new Uint8Array(width * height);
        fillPolygonSimple(tempMask, width, height, points);
        
        // XOR with existing mask
        for (let i = 0; i < mask.length; i++) {
            mask[i] ^= tempMask[i];
        }
    });
    
    // Apply mask to HU data
    for (let i = 0; i < mask.length; i++) {
        if (mask[i]) {
            huData[i] = huValue;
        }
    }
}

// Simple polygon fill for single polygon
// Export modified DICOM files
function buildSeriesDescriptionForExport() {
    const inputName = (document.getElementById('imageSetName')?.value || '').trim();
    const baseName = inputName || getDefaultSeriesName();
    let pairs = window.tempExportPairs;
    if (!pairs || !pairs.length) {
        pairs = [];
        roiData.forEach(roi => {
            if (roi.selected) {
                const hu = (roi.huValue != null && roi.huValue !== '')
                    ? roi.huValue
                    : parseInt(document.getElementById('defaultHU')?.value || '1000');
                pairs.push(`${roi.name} ${hu}HU`);
            }
        });
    } else {
        pairs = pairs.map(s => s.replace(/_/g, ' ').replace(/HU$/, ' HU'));
    }
    const suffix = pairs.length ? ` | ${pairs.join(' | ')}` : ' | NoROI';
    return `${baseName}${suffix}`;
}
// Export modified DICOM files
async function exportModifiedDICOM(processedCTs, options = {}) {
    updateStatus('Exporting modified DICOM files...');

    // Use Image Set Name (or default) as base; append burned structure names for SeriesDescription only
    const inputName = (document.getElementById('imageSetName')?.value || '').trim();
    const baseName = options.seriesDescriptionOverride ? options.seriesDescriptionOverride.split('|')[0].trim() : (inputName || getDefaultSeriesName());
    let burnedNames = [];
    if (Array.isArray(window.tempExportPairs) && window.tempExportPairs.length) {
        // tempExportPairs like ["ITV_1000HU", ...] → extract names before first underscore
        burnedNames = window.tempExportPairs.map(s => String(s).split('_')[0]).filter(Boolean);
    } else if (Array.isArray(roiData) && roiData.length) {
        burnedNames = roiData.filter(r => r.selected).map(r => r.name);
    }
    const seriesDescription = options.seriesDescriptionOverride || (burnedNames.length ? `${baseName} | ${burnedNames.join(' | ')}` : baseName);
    // Keep folder grouping readable: base name only
    const folderName = (options.folderNameOverride || `${baseName}`).replace(/\s+/g, '_');
    // Zip filename should contain burned ROI name(s)
    const sanitize = (s) => String(s).trim().replace(/[^A-Za-z0-9._-]+/g, '_');
    const roiPart = options.zipNameSuffix ? sanitize(options.zipNameSuffix) : (burnedNames.length ? burnedNames.map(sanitize).join('_') : 'NoROI');
    const zipFilename = `${sanitize(baseName)}__${roiPart}.zip`;

    // Prepare ZIP
    const zip = new JSZip();
    const dir = zip.folder(folderName);
    // Create new UIDs exactly as Python but keep raw-structure compatible (in-place)
    // We will generate values that fit within existing element lengths.
    // Probe lengths from the first slice (usually consistent across series).
    const firstDS = processedCTs[0]?.dataSet;
    const studyLen = firstDS?.elements?.x0020000d?.length || 64;
    const seriesLen = firstDS?.elements?.x0020000e?.length || 64;
    const frameLen = firstDS?.elements?.x00200052?.length || 64;
    const sopLen = firstDS?.elements?.x00080018?.length || 64;
    const descLen = firstDS?.elements?.x0008103e?.length || 64;

    // Helper: generate numeric UID that fits into existing length
    const makeUIDForLen = (maxLen) => {
        let uid = `2.25.${Date.now()}${Math.floor(Math.random()*1e12)}`;
        if (uid.length > maxLen) uid = uid.slice(0, maxLen);
        while (uid.endsWith('.')) uid = uid.slice(0, -1);
        // Ensure at least something valid
        if (uid.length < 3) uid = '2.25';
        // Make even length by trimming if needed (element storage will pad)
        return uid;
    };
    const writeASCIIInto = (byteArray, offset, maxLen, str, padNull = true) => {
        const bytes = Array.from(String(str)).map(ch => ch.charCodeAt(0));
        const L = Math.min(maxLen, bytes.length);
        // pad the field first
        for (let i = 0; i < maxLen; i++) byteArray[offset + i] = padNull ? 0x00 : 0x20;
        for (let i = 0; i < L; i++) byteArray[offset + i] = bytes[i];
    };

    const newStudyUID = makeUIDForLen(studyLen);
    const newSeriesUID = makeUIDForLen(seriesLen);
    const newFrameUID = makeUIDForLen(frameLen);

    // (removed duplicate helper definitions)

    for (let index = 0; index < processedCTs.length; index++) {
        const ctData = processedCTs[index];
        if (!ctData.modifiedPixelData || !ctData.byteArray) continue;
        // Minimal (Python-like) path: in-place replacement using original encoding
        const dataSet = ctData.dataSet;
        const pixelBytes = new Uint8Array(ctData.modifiedPixelData.buffer);
        const pixelDataElement = dataSet.elements.x7fe00010;
        if (!pixelDataElement) continue;
        const newByteArray = new Uint8Array(ctData.byteArray.length);
        newByteArray.set(ctData.byteArray);
        // Replace Pixel Data only (same size)
        newByteArray.set(pixelBytes, pixelDataElement.dataOffset);

        // Generate a per-instance SOP UID that fits the existing field
        const newSOPUID = makeUIDForLen(sopLen);
        // Update UI VRs: Study (0020,000D), Series (0020,000E), Frame (0020,0052), SOP (0008,0018)
        const eStudy = dataSet.elements.x0020000d;
        const eSeries = dataSet.elements.x0020000e;
        const eFrame = dataSet.elements.x00200052;
        const eSOP = dataSet.elements.x00080018;
        if (eStudy) writeASCIIInto(newByteArray, eStudy.dataOffset, Math.min(eStudy.length, studyLen), newStudyUID, true);
        if (eSeries) writeASCIIInto(newByteArray, eSeries.dataOffset, Math.min(eSeries.length, seriesLen), newSeriesUID, true);
        if (eFrame)  writeASCIIInto(newByteArray, eFrame.dataOffset,  Math.min(eFrame.length, frameLen),  newFrameUID,  true);
        if (eSOP)   writeASCIIInto(newByteArray, eSOP.dataOffset,   Math.min(eSOP.length, sopLen),   newSOPUID,   true);

        // Update SeriesDescription (0008,103E) LO (space padded) if present
        const eSeriesDesc = dataSet.elements.x0008103e;
        if (eSeriesDesc) writeASCIIInto(newByteArray, eSeriesDesc.dataOffset, Math.min(eSeriesDesc.length, descLen), seriesDescription, false);

        // Update file meta MediaStorageSOPInstanceUID (0002,0003) if parsed in dataset structure
        const eMsSOP = dataSet.elements.x00020003;
        if (eMsSOP) writeASCIIInto(newByteArray, eMsSOP.dataOffset, eMsSOP.length, newSOPUID, true);

        // Optional: BurnedInAnnotation (0028,0301) CS → "YES" (in-place only if exists)
        const eBurned = dataSet.elements.x00280301;
        if (eBurned) writeASCIIInto(newByteArray, eBurned.dataOffset, eBurned.length, 'YES', false);

        // Optional: DerivationDescription (0008,2111) ST → append "Burned: <ROI1 | ROI2>" (if exists)
        const eDeriv = dataSet.elements.x00082111;
        if (eDeriv) {
            let existing = '';
            try { existing = dataSet.string('x00082111') || ''; } catch (ex) { existing = ''; }
            const appendText = options.derivationText || (Array.isArray(burnedNames) && burnedNames.length ? `Burned: ${burnedNames.join(' | ')}` : '');
            const finalText = appendText ? (existing ? `${existing} | ${appendText}` : appendText) : existing;
            writeASCIIInto(newByteArray, eDeriv.dataOffset, eDeriv.length, finalText, false);
        }

        const filename = `CT_${String(index + 1).padStart(4, '0')}.dcm`;
        dir.file(filename, newByteArray);
    }

    const blob = await zip.generateAsync({ type: 'blob', compression: 'DEFLATE', compressionLevel: 9 });
    const url = URL.createObjectURL(blob);
    await downloadFile(url, zipFilename);
    URL.revokeObjectURL(url);
    updateStatus('Export complete!');
}

// Export multiple burned series into a single ZIP.
// seriesList: array of { processedCTs, roiName, hu }
async function exportMultipleSeriesToOneZip(seriesList) {
    updateStatus('Exporting multiple series to one ZIP...');

    const inputName = (document.getElementById('imageSetName')?.value || '').trim();
    const baseName = inputName || getDefaultSeriesName();
    const sanitize = (s) => String(s).trim().replace(/[^A-Za-z0-9._-]+/g, '_');

    const zip = new JSZip();
    const allRoiNames = [];

    for (const entry of seriesList) {
        const processedCTs = entry.processedCTs;
        const roiName = entry.roiName || 'ROI';
        allRoiNames.push(roiName);

        if (!processedCTs || !processedCTs.length) continue;

        const firstDS = processedCTs[0]?.dataSet;
        const studyLen = firstDS?.elements?.x0020000d?.length || 64;
        const seriesLen = firstDS?.elements?.x0020000e?.length || 64;
        const frameLen = firstDS?.elements?.x00200052?.length || 64;
        const sopLen = firstDS?.elements?.x00080018?.length || 64;
        const descLen = firstDS?.elements?.x0008103e?.length || 64;

        const makeUIDForLen = (maxLen) => {
            let uid = `2.25.${Date.now()}${Math.floor(Math.random()*1e12)}`;
            if (uid.length > maxLen) uid = uid.slice(0, maxLen);
            while (uid.endsWith('.')) uid = uid.slice(0, -1);
            if (uid.length < 3) uid = '2.25';
            return uid;
        };
        const writeASCIIInto = (byteArray, offset, maxLen, str, padNull = true) => {
            const bytes = Array.from(String(str)).map(ch => ch.charCodeAt(0));
            const L = Math.min(maxLen, bytes.length);
            for (let i = 0; i < maxLen; i++) byteArray[offset + i] = padNull ? 0x00 : 0x20;
            for (let i = 0; i < L; i++) byteArray[offset + i] = bytes[i];
        };

        const newStudyUID = makeUIDForLen(studyLen);
        const newSeriesUID = makeUIDForLen(seriesLen);
        const newFrameUID = makeUIDForLen(frameLen);

        const seriesDescription = `${baseName} | ${roiName}`;
        const folderName = `${sanitize(baseName)}__${sanitize(roiName)}`;
        const dir = zip.folder(folderName);

        for (let index = 0; index < processedCTs.length; index++) {
            const ctData = processedCTs[index];
            if (!ctData.modifiedPixelData || !ctData.byteArray) continue;
            const dataSet = ctData.dataSet;
            const pixelBytes = new Uint8Array(ctData.modifiedPixelData.buffer);
            const pixelDataElement = dataSet.elements.x7fe00010;
            if (!pixelDataElement) continue;
            const newByteArray = new Uint8Array(ctData.byteArray.length);
            newByteArray.set(ctData.byteArray);
            newByteArray.set(pixelBytes, pixelDataElement.dataOffset);

            const newSOPUID = makeUIDForLen(sopLen);
            const eStudy = dataSet.elements.x0020000d;
            const eSeries = dataSet.elements.x0020000e;
            const eFrame = dataSet.elements.x00200052;
            const eSOP = dataSet.elements.x00080018;
            if (eStudy) writeASCIIInto(newByteArray, eStudy.dataOffset, Math.min(eStudy.length, studyLen), newStudyUID, true);
            if (eSeries) writeASCIIInto(newByteArray, eSeries.dataOffset, Math.min(eSeries.length, seriesLen), newSeriesUID, true);
            if (eFrame)  writeASCIIInto(newByteArray, eFrame.dataOffset,  Math.min(eFrame.length, frameLen),  newFrameUID,  true);
            if (eSOP)   writeASCIIInto(newByteArray, eSOP.dataOffset,   Math.min(eSOP.length, sopLen),   newSOPUID,   true);

            const eSeriesDesc = dataSet.elements.x0008103e;
            if (eSeriesDesc) writeASCIIInto(newByteArray, eSeriesDesc.dataOffset, Math.min(eSeriesDesc.length, descLen), seriesDescription, false);
            const eMsSOP = dataSet.elements.x00020003;
            if (eMsSOP) writeASCIIInto(newByteArray, eMsSOP.dataOffset, eMsSOP.length, newSOPUID, true);
            const eBurned = dataSet.elements.x00280301;
            if (eBurned) writeASCIIInto(newByteArray, eBurned.dataOffset, eBurned.length, 'YES', false);
            const eDeriv = dataSet.elements.x00082111;
            if (eDeriv) writeASCIIInto(newByteArray, eDeriv.dataOffset, eDeriv.length, `Burned: ${roiName}`, false);

            const filename = `CT_${String(index + 1).padStart(4, '0')}.dcm`;
            dir.file(filename, newByteArray);
        }
    }

    // Create a single ZIP file with all ROIs included in its filename
    const roiPart = allRoiNames.length ? allRoiNames.map(sanitize).join('_') : 'NoROI';
    const zipFilename = `${sanitize(baseName)}__${roiPart}.zip`;
    const blob = await zip.generateAsync({ type: 'blob', compression: 'DEFLATE', compressionLevel: 9 });
    const url = URL.createObjectURL(blob);
    await downloadFile(url, zipFilename);
    URL.revokeObjectURL(url);
}

// Download single file
async function downloadFile(url, filename) {
    const a = document.createElement('a');
    a.href = url;
    a.download = filename;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
}

// Generate simple UID (simplified version)
function generateUID() {
    const timestamp = Date.now();
    const random = Math.floor(Math.random() * 1000000);
    return `2.25.${timestamp}${random}`;
}

function fillPolygonSimple(mask, width, height, points) {
    if (points.length < 3) return;
    
    // Find bounding box
    let minX = width, maxX = 0, minY = height, maxY = 0;
    points.forEach(([x, y]) => {
        minX = Math.min(minX, x);
        maxX = Math.max(maxX, x);
        minY = Math.min(minY, y);
        maxY = Math.max(maxY, y);
    });
    
    // Scan each row in the bounding box
    for (let y = minY; y <= maxY; y++) {
        if (y < 0 || y >= height) continue;
        
        // Find intersections with polygon edges
        const intersections = [];
        for (let i = 0; i < points.length; i++) {
            const p1 = points[i];
            const p2 = points[(i + 1) % points.length];
            
            if ((p1[1] <= y && p2[1] > y) || (p2[1] <= y && p1[1] > y)) {
                const x = p1[0] + (y - p1[1]) * (p2[0] - p1[0]) / (p2[1] - p1[1]);
                intersections.push(x);
            }
        }
        
        // Sort intersections
        intersections.sort((a, b) => a - b);
        
        // Fill between pairs of intersections
        for (let i = 0; i < intersections.length; i += 2) {
            if (i + 1 < intersections.length) {
                const x1 = Math.max(0, Math.floor(intersections[i]));
                const x2 = Math.min(width - 1, Math.ceil(intersections[i + 1]));
                
                for (let x = x1; x <= x2; x++) {
                    const idx = y * width + x;
                    huData[idx] = huValue;
                }
            }
        }
    }
}

// Open viewer immediately for preview (before burn-in)
async function openViewerForPreview() {
    try {
        // Initialize canvas sizes
        setTimeout(() => {
            const viewportContainers = document.querySelectorAll('.viewport-container');
            viewportContainers.forEach(container => {
                const canvas = container.querySelector('canvas');
                if (canvas) {
                    const rect = container.getBoundingClientRect();
                    canvas.width = Math.floor(rect.width);
                    canvas.height = Math.floor(rect.height);
                }
            });
        }, 100);
        
        // Initialize simple viewer
        await initializeSimpleViewer();
        displaySimpleViewer();

        // Adapt footer note maxlength based on image width and font (3 lines, full width)
        try {
            const first = (ctFiles && ctFiles[0] && ctFiles[0].dataSet) ? ctFiles[0].dataSet : null;
            const width = first ? (first.uint16 ? (first.uint16(Tag.Columns) || 512) : 512) : 512;
            const charWidth = Math.max(6, Math.round(FOOTER_FONT_PX * 0.6));
            const usable = Math.max(0, width); // full image width
            const perLine = Math.max(0, Math.floor(usable / charWidth));
            const maxChars = Math.max(0, perLine * 3);
            const noteEl = document.getElementById('footerNote');
            if (noteEl) noteEl.maxLength = Math.max(0, maxChars);
        } catch (e) { /* ignore */ }
    } catch (error) {
        console.error('Error opening viewer:', error);
        showMessage('error', 'Failed to open viewer: ' + error.message);
    }
}

// Viewer Functions
async function openDicomViewer(processedCTs) {
    // This function is no longer needed with single interface
    // The viewer is already open and we just need to refresh it
    displaySimpleViewer();
}

// Viewport interaction state management
const viewportState = {
    axial: { 
        zoom: 1, 
        panX: 0, 
        panY: 0, 
        mouseDown: false, 
        rightMouseDown: false,
        lastMouseX: 0,
        lastMouseY: 0
    },
    sagittal: { 
        zoom: 1, 
        panX: 0, 
        panY: 0, 
        mouseDown: false, 
        rightMouseDown: false,
        lastMouseX: 0,
        lastMouseY: 0,
        currentSliceX: 0  // Track current sagittal slice
    },
    coronal: { 
        zoom: 1, 
        panX: 0, 
        panY: 0, 
        mouseDown: false, 
        rightMouseDown: false,
        lastMouseX: 0,
        lastMouseY: 0,
        currentSliceY: 0  // Track current coronal slice
    }
};

// Simple fallback viewer without Cornerstone3D
async function initializeSimpleViewer() {
    // Initialize processedCTData as empty if not set
    if (!processedCTData || processedCTData.length === 0) {
        processedCTData = [];
    }
    
    const seriesInit = getActiveSeries();
    window.simpleViewerData = {
        currentSlice: Math.floor((seriesInit.length || 1) / 2),
        isShowingBurned: false,
        windowWidth: Math.max(1, (ctWindowRange.max || 0) - (ctWindowRange.min || 0)),
        windowLevel: ((ctWindowRange.max || 0) + (ctWindowRange.min || 0)) / 2
    };
    
    // Setup mouse interactions for viewports
    setupViewportInteractions();
    
    syncWindowInputsToActiveTab();
    applyWindowForActiveTab();
    
    // Display initial slice
    setTimeout(() => {
        displaySimpleViewer();
    }, 100);
    
    // Update slider
    const slider = document.getElementById('sliceSlider');
    if (slider) {
        slider.min = 0;
        slider.max = Math.max(0, seriesInit.length - 1);
        slider.value = window.simpleViewerData.currentSlice;
    }
    
    const sliceInfo = document.getElementById('sliceInfo');
    if (sliceInfo) {
        sliceInfo.textContent = `${window.simpleViewerData.currentSlice + 1}/${seriesInit.length}`;
    }
}

function getActiveSeries() {
    if (activeTab === 'mr') {
        if (mrPreviewActive && Array.isArray(mrBlendedSlices) && mrBlendedSlices.length) return mrBlendedSlices;
        if (mrPreviewActive && Array.isArray(mrResampledSlices) && mrResampledSlices.length) return mrResampledSlices;
        return Array.isArray(ctFiles) ? ctFiles : [];
    }
    const usePreview = (window.previewMode && previewIsRealBurn && Array.isArray(previewBurnedCTData) && previewBurnedCTData.length);
    if (usePreview) return previewBurnedCTData;
    if (window.simpleViewerData && window.simpleViewerData.isShowingBurned && Array.isArray(processedCTData) && processedCTData.length) return processedCTData;
    return Array.isArray(ctFiles) ? ctFiles : [];
}

// Setup mouse interactions for viewports
function setupViewportInteractions() {
    const viewports = ['axial', 'sagittal', 'coronal'];
    
    viewports.forEach(viewportName => {
        const viewport = document.getElementById(`viewport-${viewportName}`);
        if (!viewport) return;
        
        // Check if we already have listeners (avoid duplicates)
        if (viewport.hasAttribute('data-listeners-added')) return;
        viewport.setAttribute('data-listeners-added', 'true');
        
    // Prevent context menu on right click
    viewport.addEventListener('contextmenu', (e) => {
        e.preventDefault();
        centerCrosshairAt(viewportName, e);
        return false;
    });
        
        // Mouse wheel for slice navigation or zoom
        viewport.addEventListener('wheel', (e) => handleWheel(e, viewportName), { passive: false });
        
        // Mouse down for pan or window/level or crosshair drag (Shift+Left)
        viewport.addEventListener('mousedown', (e) => handleMouseDown(e, viewportName));
        
        // Mouse move for dragging
        viewport.addEventListener('mousemove', (e) => handleMouseMove(e, viewportName));
        
        // Mouse up to end dragging
        viewport.addEventListener('mouseup', (e) => handleMouseUp(e, viewportName));
        
        // Mouse leave to end dragging
        viewport.addEventListener('mouseleave', (e) => handleMouseUp(e, viewportName));
        
        // Update cursor style
        viewport.style.cursor = 'grab';
    });
}

// Handle mouse wheel events
function handleWheel(e, viewportName) {
    e.preventDefault();
    
    if (e.ctrlKey || e.metaKey) {
        // Ctrl+Scroll for zoom. Zoom towards crosshair center on all views
        // to keep planes synchronized under zoom.
        const scaleDelta = e.deltaY > 0 ? 0.9 : 1.1;

        const viewports = ['axial', 'sagittal', 'coronal'];
        // Capture old+new zooms
        const oldZoom = {};
        const newZoom = {};
        viewports.forEach(vp => {
            oldZoom[vp] = viewportState[vp].zoom;
            newZoom[vp] = clampZoom(oldZoom[vp] * scaleDelta);
        });

        // Apply zooms
        viewports.forEach(vp => { viewportState[vp].zoom = newZoom[vp]; });

        // Adjust pans to anchor the crosshair intersection point in each view
        viewports.forEach(vp => {
            const canvas = document.getElementById(`viewport-${vp}`);
            if (!canvas) return;
            const cross = getCrosshairScreenPoint(vp);
            const anchorX = cross.x;
            const anchorY = cross.y;
            adjustPanForZoom(vp, oldZoom[vp], newZoom[vp], anchorX, anchorY);
        });

        displaySimpleViewer();
    } else {
        // Normal scroll for slice navigation
        // Axial: mouse wheel UP -> superior (next slice), DOWN -> inferior (previous slice)
        // Typical wheel event: deltaY < 0 on wheel up, > 0 on wheel down.
        const wheelUp = e.deltaY < 0;
        
        // Navigate based on which viewport was scrolled
        if (viewportName === 'axial') {
            const delta = wheelUp ? 1 : -1;
            navigateSlice(delta);
        } else if (viewportName === 'sagittal') {
            // Navigate sagittal slice (X axis)
            const volume = window.volumeData;
            if (volume) {
                const delta = (e.deltaY < 0) ? 1 : -1; // wheel up -> +X
                const currentX = viewportState.sagittal.currentSliceX || Math.floor(volume.width / 2);
                const newX = Math.max(0, Math.min(volume.width - 1, currentX + delta));
                // Update state and re-render both sagittal and coronal to sync crosshair
                viewportState.sagittal.currentSliceX = newX;
                renderSagittalView(volume, newX);
                renderCoronalView(volume, viewportState.coronal.currentSliceY || Math.floor(volume.height / 2));
            }
        } else if (viewportName === 'coronal') {
            // Navigate coronal slice (Y axis)
            const volume = window.volumeData;
            if (volume) {
                const delta = (e.deltaY < 0) ? 1 : -1; // wheel up -> +Y
                const currentY = viewportState.coronal.currentSliceY || Math.floor(volume.height / 2);
                const newY = Math.max(0, Math.min(volume.height - 1, currentY + delta));
                // Update state and re-render both coronal and sagittal to sync crosshair
                viewportState.coronal.currentSliceY = newY;
                renderCoronalView(volume, newY);
                renderSagittalView(volume, viewportState.sagittal.currentSliceX || Math.floor(volume.width / 2));
            }
        }
    }
}

function clampZoom(z) {
    return Math.max(0.1, Math.min(10, z));
}

// Adjust pan so that the given anchor screen point stays fixed when zoom changes
function adjustPanForZoom(viewportName, zOld, zNew, anchorX, anchorY) {
    const canvas = document.getElementById(`viewport-${viewportName}`);
    if (!canvas) return;
    const state = viewportState[viewportName];
    const centerX = canvas.width / 2;
    const centerY = canvas.height / 2;
    const tX = state.panX;
    const tY = state.panY;

    // Model/base coords of the anchor point before zoom
    const pX = (anchorX - centerX - tX) / zOld + centerX;
    const pY = (anchorY - centerY - tY) / zOld + centerY;

    // New pan to keep same screen position after zoom
    const newPanX = anchorX - (pX - centerX) * zNew - centerX;
    const newPanY = anchorY - (pY - centerY) * zNew - centerY;

    state.panX = newPanX;
    state.panY = newPanY;
}

// Compute screen position of crosshair intersection in a given view
function getCrosshairScreenPoint(viewName) {
    const geom = window.viewGeom && window.viewGeom[viewName];
    if (!geom) return { x: 0, y: 0 };
    let dataX = 0, dataY = 0;
    if (viewName === 'axial') {
        dataX = viewportState.sagittal.currentSliceX || 0;
        dataY = viewportState.coronal.currentSliceY || 0;
    } else if (viewName === 'sagittal') {
        const y = viewportState.coronal.currentSliceY || 0;
        const z = window.simpleViewerData.currentSlice || 0;
        dataX = y; // width = Y
        dataY = (geom.dataHeight - 1 - z); // height = Z, flipped
    } else if (viewName === 'coronal') {
        const x = viewportState.sagittal.currentSliceX || 0;
        const z = window.simpleViewerData.currentSlice || 0;
        dataX = x; // width = X
        dataY = (geom.dataHeight - 1 - z); // height = Z, flipped
    }
    // Data -> base coords (within display rect)
    const scaleX = geom.displayWidth / geom.dataWidth;
    const scaleY = geom.displayHeight / geom.dataHeight;
    const baseX = geom.offsetX + (dataX + 0.5) * scaleX;
    const baseY = geom.offsetY + (dataY + 0.5) * scaleY;
    // Apply pan/zoom about canvas center
    const cx = geom.canvasWidth / 2;
    const cy = geom.canvasHeight / 2;
    const screenX = (baseX - cx) * geom.zoom + cx + geom.panX;
    const screenY = (baseY - cy) * geom.zoom + cy + geom.panY;
    return { x: screenX, y: screenY };
}

// Handle mouse down events
function handleMouseDown(e, viewportName) {
    const state = viewportState[viewportName];
    const rect = e.target.getBoundingClientRect();
    
    state.lastMouseX = e.clientX - rect.left;
    state.lastMouseY = e.clientY - rect.top;
    
    if (e.button === 0 && e.shiftKey) {
        // Shift+Left: begin crosshair drag
        window.crosshairDrag = { active: true, view: viewportName };
        e.target.style.cursor = 'crosshair';
    } else if (e.button === 0) {
        // Left click for pan
        state.mouseDown = true;
        e.target.style.cursor = 'grabbing';
    } else if (e.button === 2) {
        // Right click for window/level
        state.rightMouseDown = true;
        e.target.style.cursor = 'crosshair';
    }
}

// Handle mouse move events
function handleMouseMove(e, viewportName) {
    const state = viewportState[viewportName];
    
    if (!state.mouseDown && !state.rightMouseDown) return;
    if (window.crosshairDrag && window.crosshairDrag.active && window.crosshairDrag.view === viewportName) {
        updateCrosshairFromMouse(viewportName, e);
        return;
    }
    
    const rect = e.target.getBoundingClientRect();
    const currentX = e.clientX - rect.left;
    const currentY = e.clientY - rect.top;
    
    const deltaX = currentX - state.lastMouseX;
    const deltaY = currentY - state.lastMouseY;
    
    if (state.mouseDown) {
        // Pan - apply only to current view
        state.panX += deltaX;
        state.panY += deltaY;
        displaySimpleViewer();
    } else if (state.rightMouseDown) {
        // Window/Level adjustment - applies to all views already
        adjustWindowLevel(deltaX, deltaY);
    }
    
    state.lastMouseX = currentX;
    state.lastMouseY = currentY;
}

// Handle mouse up events
function handleMouseUp(e, viewportName) {
    const state = viewportState[viewportName];
    
    if (state.mouseDown) {
        state.mouseDown = false;
        e.target.style.cursor = 'grab';
    }
    
    if (state.rightMouseDown) {
        state.rightMouseDown = false;
        e.target.style.cursor = 'default';
    }
    if (window.crosshairDrag && window.crosshairDrag.active && window.crosshairDrag.view === viewportName) {
        window.crosshairDrag.active = false;
        e.target.style.cursor = 'grab';
    }
}

// Navigate to a different slice
function navigateSlice(delta) {
    if (!window.simpleViewerData) return;
    const series = getActiveSeries();
    if (!series || series.length === 0) return;

    const newSlice = window.simpleViewerData.currentSlice + delta;
    if (newSlice >= 0 && newSlice < series.length) {
        window.simpleViewerData.currentSlice = newSlice;
        displaySimpleViewer();
        
        // Update slice slider if it exists
        const slider = document.getElementById('sliceSlider');
        if (slider) {
            slider.value = newSlice;
        }
    }
}

// Adjust window width and level
function adjustWindowLevel(deltaX, deltaY) {
    // Right-drag WL should always adjust CT windowing (even on MR tab)
    const range = ctWindowRange || { min: -160, max: 240 };
    let ww = Math.max(1, (range.max - range.min) + deltaX * 2);
    let wl = ((range.max + range.min) / 2) - deltaY * 2;
    const min = wl - ww / 2;
    const max = wl + ww / 2;
    ctWindowRange = { min, max };
    updateWindowRangeLabels();
    applyWindowForActiveTab();
    displaySimpleViewer();
}

function displaySimpleViewer() {
    if (DEBUG) console.log('displaySimpleViewer - ROI data check:', {
        hasPatientMark: !!window.RTSSMarks,
        numPatientMarks: window.RTSSMarks?.length,
        hasRoiData: !!window.roiData,
        numRois: window.roiData?.length
    });
    
    if (!ctFiles || ctFiles.length === 0) {
        console.error('No CT files available to display');
        return;
    }
    
    const slice = window.simpleViewerData.currentSlice;

    const series = getActiveSeries();

    const ctData = series[slice];
    
    if (!ctData) {
        console.error('No CT data for slice:', slice);
        return;
    }
    
    if (!ctData.dataSet) {
        console.error('CT data missing dataSet property');
        return;
    }
    
    
    // Render to axial viewport canvas
    const canvas = document.getElementById('viewport-axial');
    if (!canvas) {
        console.error('Canvas element not found');
        return;
    }

    const ctx = canvas.getContext('2d', { willReadFrequently: true });
    const state = viewportState.axial;

    // Get image dimensions from dataset
    let width = 512, height = 512;
    if (ctData.dataSet) {
        width = ctData.dataSet.uint16(Tag.Columns) || 512;
        height = ctData.dataSet.uint16(Tag.Rows) || 512;
    }

    // Fit viewport and prepare canvas size
    const container = canvas.parentElement;
    const containerRect = container.getBoundingClientRect();
    canvas.width = containerRect.width;
    canvas.height = containerRect.height;

    // Clear and set transforms (pan/zoom)
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.save();
    ctx.translate(canvas.width / 2 + state.panX, canvas.height / 2 + state.panY);
    ctx.scale(state.zoom, state.zoom);
    ctx.translate(-canvas.width / 2, -canvas.height / 2);

    // Compute display rectangle preserving aspect ratio
    const dataAspectRatio = height / width;
    const viewportAspectRatio = canvas.height / canvas.width;
    let displayWidth, displayHeight;
    if (dataAspectRatio > viewportAspectRatio) {
        displayHeight = canvas.height * 0.9;
        displayWidth = displayHeight / dataAspectRatio;
    } else {
        displayWidth = canvas.width * 0.9;
        displayHeight = displayWidth * dataAspectRatio;
    }
    const offsetX = (canvas.width - displayWidth) / 2;
    const offsetY = (canvas.height - displayHeight) / 2;
    
    // Get pixel data element
    let pixelData;
    if (!ctData.dataSet.elements || !ctData.dataSet.elements.x7fe00010) {
        console.error('No pixel data element found in dataSet');
        return;
    }
    
    const pixelDataElement = ctData.dataSet.elements.x7fe00010;
    const offset = pixelDataElement.dataOffset;
    const length = pixelDataElement.length;
    
    
    // For processed data, use modifiedPixelData if available
    if (ctData.modifiedPixelData) {
        pixelData = ctData.modifiedPixelData;
    } else if (ctData.byteArray) {
        // Extract from byte array
        try {
            pixelData = new Int16Array(ctData.byteArray.buffer, offset, length / 2);
        } catch (e) {
            console.error('Failed with ctData.byteArray:', e.message);
            // Try alternative extraction
            try {
                pixelData = new Int16Array(ctData.dataSet.byteArray.buffer, offset, length / 2);
            } catch (e2) {
                console.error('Failed with dataSet.byteArray:', e2.message);
                return;
            }
        }
    } else if (ctData.dataSet.byteArray) {
        // Use dataSet's byte array
        try {
            pixelData = new Int16Array(ctData.dataSet.byteArray.buffer, offset, length / 2);
        } catch (e) {
            console.error('Failed to extract from dataSet.byteArray:', e.message);
            return;
        }
    } else {
        console.error('No byte array found for pixel data extraction');
        return;
    }
    
    // Check if we got valid pixel data
    if (!pixelData || pixelData.length === 0) {
        console.error('Pixel data is empty or invalid');
        return;
    }
    
    
    // Get rescale values
    let slope = 1, intercept = 0;
    if (ctData.dataSet) {
        slope = ctData.dataSet.floatString(Tag.RescaleSlope) || 1;
        intercept = ctData.dataSet.floatString(Tag.RescaleIntercept) || 0;
    }
    
    // Create image data
    const imageData = ctx.createImageData(width, height);
    const data = imageData.data;
    
    const windowWidth = window.simpleViewerData.windowWidth;
    const windowLevel = window.simpleViewerData.windowLevel;
    const windowMin = windowLevel - windowWidth / 2;
    const windowMax = windowLevel + windowWidth / 2;
    
    
    // Ensure we have the right amount of data
    if (pixelData.length !== width * height) {
        console.warn('Pixel data length mismatch:', pixelData.length, 'vs expected:', width * height);
    }
    
    const pixelsToProcess = Math.min(pixelData.length, width * height);
    let minHU = Infinity, maxHU = -Infinity;
    let minGray = 255, maxGray = 0;
    
    for (let i = 0; i < pixelsToProcess; i++) {
        const hu = pixelData[i] * slope + intercept;
        if (hu < minHU) minHU = hu;
        if (hu > maxHU) maxHU = hu;
        
        let gray = ((hu - windowMin) / windowWidth) * 255;
        gray = Math.max(0, Math.min(255, gray));
        
        if (gray < minGray) minGray = gray;
        if (gray > maxGray) maxGray = gray;
        
        const idx = i * 4;
        data[idx] = gray;
        data[idx + 1] = gray;
        data[idx + 2] = gray;
        data[idx + 3] = 255;
    }
    
    
    // Blit to a temporary canvas so we can draw with transforms
    try {
        const tempCanvas = document.createElement('canvas');
        tempCanvas.width = width;
        tempCanvas.height = height;
        const tctx = tempCanvas.getContext('2d');
        tctx.putImageData(imageData, 0, 0);
        // Draw scaled into viewport
        ctx.drawImage(tempCanvas, offsetX, offsetY, displayWidth, displayHeight);
    } catch (error) {
        console.error('Error rendering image:', error);
        // Show error message on canvas
        ctx.fillStyle = '#ff0000';
        ctx.font = '16px Arial';
        ctx.fillText('Error loading image', 10, 30);
        ctx.fillText(error.message, 10, 50);
    }
    
    // Persist display geometry for interactions
    window.viewGeom = window.viewGeom || {};
    window.viewGeom.axial = {
        offsetX, offsetY, displayWidth, displayHeight,
        dataWidth: width, dataHeight: height,
        canvasWidth: canvas.width, canvasHeight: canvas.height,
        panX: state.panX, panY: state.panY, zoom: state.zoom
    };

    // Draw ROI overlays on axial view using same display rect (offset + scale)
    const axialDisplay = {
        offsetX,
        offsetY,
        displayWidth,
        displayHeight,
        dataWidth: width,
        dataHeight: height
    };
    drawROIOverlayOnCanvas(ctx, ctData, slice, width, height, axialDisplay);
    // Draw crosshair
    drawCrosshairAxial(ctx, axialDisplay, width, height);

    // No overlay footer during preview; preview displays burned pixels only
    
    // Restore context state
    ctx.restore();
    
    // Create/update sagittal and coronal views
    renderOtherViews(slice);
    
    // Update slice info
    const sliderEl = document.getElementById('sliceSlider');
    if (sliderEl) {
        sliderEl.value = slice;
        sliderEl.max = Math.max(0, series.length - 1);
    }
    const sliceInfoEl = document.getElementById('sliceInfo');
    if (sliceInfoEl) {
        sliceInfoEl.textContent = `${slice + 1}/${series.length}`;
    }
    
    // Update viewport info
    const infoElement = document.getElementById('info-axial');
    if (infoElement) {
        const seriesLen = getActiveSeries().length || 0;
        infoElement.innerHTML = `Slice: ${slice + 1}/${seriesLen}<br>WL: ${windowWidth}/${windowLevel}`;
    }
}

// Create volume data for MPR reconstruction
async function createVolumeData() {
    const series = getActiveSeries();
    if (!series || series.length === 0) return null;
    
    const volume = {
        data: [],
        width: 0,
        height: 0,
        depth: series.length,
        pixelSpacing: null,
        sliceThickness: null,
        sliceSpacing: null,
        imagePosition: [],
        imageOrientation: null,
        slope: 1,
        intercept: 0,
        sopUIDs: [],
        sopUIDIndex: {}
    };
    
    // Load all slices
    for (let i = 0; i < series.length; i++) {
        const ctData = series[i];
        if (!ctData.dataSet) continue;
        
        // Get dimensions from first slice
        if (i === 0) {
            volume.width = ctData.dataSet.uint16(Tag.Columns) || 512;
            volume.height = ctData.dataSet.uint16(Tag.Rows) || 512;
            volume.slope = ctData.dataSet.floatString(Tag.RescaleSlope) || 1;
            volume.intercept = ctData.dataSet.floatString(Tag.RescaleIntercept) || 0;
            
            const pixelSpacing = ctData.dataSet.string(Tag.PixelSpacing);
            if (pixelSpacing) {
                const ps = pixelSpacing.split('\\');
                volume.pixelSpacing = [parseFloat(ps[0]), parseFloat(ps[1])];
            }
            
            // Get slice thickness
            volume.sliceThickness = ctData.dataSet.floatString('x00180050') || 1.0; // SliceThickness tag
            
            const orientation = ctData.dataSet.string(Tag.ImageOrientationPatient);
            if (orientation) {
                const orient = orientation.split('\\').map(parseFloat);
                volume.imageOrientation = orient;
            }
        }
        
        // Get image position
        const position = ctData.dataSet.string(Tag.ImagePositionPatient);
        if (position) {
            const pos = position.split('\\').map(parseFloat);
            volume.imagePosition.push(pos);
        }
        // Map SOPInstanceUID -> z index
        const sop = ctData.dataSet.string(Tag.SOPInstanceUID);
        volume.sopUIDs.push(sop);
        volume.sopUIDIndex[sop] = i;
        
        // Get pixel data
        const pixelDataElement = ctData.dataSet.elements.x7fe00010;
        if (!pixelDataElement) continue;
        
        const offset = pixelDataElement.dataOffset;
        const length = pixelDataElement.length;
        
        let pixelData;
        if (ctData.modifiedPixelData) {
            pixelData = ctData.modifiedPixelData;
        } else if (ctData.byteArray) {
            pixelData = new Int16Array(ctData.byteArray.buffer, offset, length / 2);
        } else if (ctData.dataSet.byteArray) {
            pixelData = new Int16Array(ctData.dataSet.byteArray.buffer, offset, length / 2);
        }
        
        if (pixelData) {
            volume.data.push(pixelData);
        }
    }
    
    // Use slice thickness directly from DICOM header - DO NOT CALCULATE
    // SliceThickness is defined in DICOM header and must be followed exactly
    volume.sliceSpacing = volume.sliceThickness || 1.0;
    
    
    return volume;
}

// Render MPR views
async function renderOtherViews(currentSlice) {
    if (DEBUG) console.log('renderOtherViews called', { currentSlice });
    
    // Create volume data if not already created
    if (!window.volumeData) {
        if (DEBUG) console.log('Creating volume data...');
        window.volumeData = await createVolumeData();
    }
    
    const volume = window.volumeData;
    if (DEBUG) console.log('Volume data:', { hasVolume: !!volume, dataLength: volume?.data?.length });
    
    if (!volume || volume.data.length === 0) {
        if (DEBUG) console.log('No volume data, showing placeholders');
        // Show placeholder if no volume data
        renderPlaceholderViews();
        return;
    }
    
    // Initialize slice positions if not set
    if (viewportState.sagittal.currentSliceX === 0 || viewportState.sagittal.currentSliceX >= volume.width) {
        viewportState.sagittal.currentSliceX = Math.floor(volume.width / 2);
    }
    if (viewportState.coronal.currentSliceY === 0 || viewportState.coronal.currentSliceY >= volume.height) {
        viewportState.coronal.currentSliceY = Math.floor(volume.height / 2);
    }
    
    // Render sagittal view (YZ plane)
    renderSagittalView(volume, viewportState.sagittal.currentSliceX);
    
    // Render coronal view (XZ plane)
    renderCoronalView(volume, viewportState.coronal.currentSliceY);
}

function renderSagittalView(volume, sliceX) {
    if (DEBUG) console.log('renderSagittalView called', { sliceX, hasVolume: !!volume });
    
    const canvas = document.getElementById('viewport-sagittal');
    if (!canvas) {
        if (DEBUG) console.log('No sagittal canvas found');
        return;
    }
    
    // Store current slice position
    viewportState.sagittal.currentSliceX = sliceX;
    
    const ctx = canvas.getContext('2d', { willReadFrequently: true });
    const state = viewportState.sagittal;
    
    // Sagittal view dimensions
    const width = volume.height;  // Y axis
    const height = volume.depth;  // Z axis
    
    // Set canvas dimensions to viewport size
    const container = canvas.parentElement;
    const containerRect = container.getBoundingClientRect();
    canvas.width = containerRect.width;
    canvas.height = containerRect.height;
    
    // Clear canvas
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.save();
    
    // Calculate aspect ratio
    const sliceSpacing = volume.sliceSpacing || 1.0;
    const rowSpacing = volume.pixelSpacing ? volume.pixelSpacing[0] : 1.0;
    
    // Calculate the display scale to fit the viewport
    const dataAspectRatio = (height * sliceSpacing) / (width * rowSpacing);
    const viewportAspectRatio = canvas.height / canvas.width;
    
    let displayWidth, displayHeight;
    if (dataAspectRatio > viewportAspectRatio) {
        // Height-constrained
        displayHeight = canvas.height * 0.9;
        displayWidth = displayHeight / dataAspectRatio;
    } else {
        // Width-constrained
        displayWidth = canvas.width * 0.9;
        displayHeight = displayWidth * dataAspectRatio;
    }
    
    // Center the image
    const offsetX = (canvas.width - displayWidth) / 2;
    const offsetY = (canvas.height - displayHeight) / 2;
    
    // Apply transforms
    ctx.translate(canvas.width/2 + state.panX, canvas.height/2 + state.panY);
    ctx.scale(state.zoom, state.zoom);
    ctx.translate(-canvas.width/2, -canvas.height/2);
    
    // Create temporary canvas for the actual data
    const tempCanvas = document.createElement('canvas');
    tempCanvas.width = width;
    tempCanvas.height = height;
    const tempCtx = tempCanvas.getContext('2d');
    
    const imageData = tempCtx.createImageData(width, height);
    const data = imageData.data;
    
    const windowWidth = window.simpleViewerData.windowWidth;
    const windowLevel = window.simpleViewerData.windowLevel;
    const windowMin = windowLevel - windowWidth / 2;
    const windowMax = windowLevel + windowWidth / 2;
    
    // Extract sagittal slice - correct orientation
    for (let z = 0; z < volume.depth; z++) {
        const sliceData = volume.data[z];
        if (!sliceData) continue;
        
        for (let y = 0; y < volume.height; y++) {
            const srcIdx = y * volume.width + sliceX;
            // Correct orientation: flip vertically
            const dstIdx = ((height - 1 - z) * width + y) * 4;
            
            if (srcIdx < sliceData.length) {
                const hu = sliceData[srcIdx] * volume.slope + volume.intercept;
                let gray = ((hu - windowMin) / windowWidth) * 255;
                gray = Math.max(0, Math.min(255, gray));
                
                data[dstIdx] = gray;
                data[dstIdx + 1] = gray;
                data[dstIdx + 2] = gray;
                data[dstIdx + 3] = 255;
            }
        }
    }
    
    tempCtx.putImageData(imageData, 0, 0);
    
    // Draw the temp canvas to the main canvas with proper scaling
    ctx.drawImage(tempCanvas, offsetX, offsetY, displayWidth, displayHeight);
    
    // Draw ROI overlay on sagittal view with display parameters before restoring so pan/zoom apply
    // Persist display geometry for interactions
    window.viewGeom = window.viewGeom || {};
    window.viewGeom.sagittal = {
        offsetX, offsetY, displayWidth, displayHeight,
        dataWidth: width, dataHeight: height,
        canvasWidth: canvas.width, canvasHeight: canvas.height,
        panX: state.panX, panY: state.panY, zoom: state.zoom
    };
    const displayParams = {
        offsetX: offsetX,
        offsetY: offsetY,
        displayWidth: displayWidth,
        displayHeight: displayHeight,
        dataWidth: width,
        dataHeight: height
    };
    drawROIOverlaySagittal(ctx, volume, sliceX, displayParams);
    // Crosshair: vertical at coronal Y, horizontal at axial Z
    drawCrosshairSagittal(ctx, displayParams, volume);
    
    // Restore after overlay so transforms affect both
    ctx.restore();
    
    // Update info
    const infoElement = document.getElementById('info-sagittal');
    if (infoElement) {
        const sliceNum = sliceX + 1;
        const totalSlices = volume.width;
        infoElement.innerHTML = `<span>Slice: <span id="sagittal-slice">${sliceNum}/${totalSlices}</span></span><br>
                                 <span>WL: <span id="sagittal-wl">${windowWidth}/${windowLevel}</span></span>`;
    }
}

function renderCoronalView(volume, sliceY) {
    const canvas = document.getElementById('viewport-coronal');
    if (!canvas) return;
    
    // Store current slice position
    viewportState.coronal.currentSliceY = sliceY;
    
    const ctx = canvas.getContext('2d', { willReadFrequently: true });
    const state = viewportState.coronal;
    
    // Coronal view dimensions
    const width = volume.width;   // X axis
    const height = volume.depth;  // Z axis
    
    // Set canvas dimensions to viewport size
    const container = canvas.parentElement;
    const containerRect = container.getBoundingClientRect();
    canvas.width = containerRect.width;
    canvas.height = containerRect.height;
    
    // Clear canvas
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.save();
    
    // Calculate aspect ratio
    const pixelSpacingX = volume.pixelSpacing ? volume.pixelSpacing[1] : 1.0;
    const sliceSpacing = volume.sliceSpacing || 1.0;
    
    // Calculate the display scale to fit the viewport
    const dataAspectRatio = (height * sliceSpacing) / (width * pixelSpacingX);
    const viewportAspectRatio = canvas.height / canvas.width;
    
    let displayWidth, displayHeight;
    if (dataAspectRatio > viewportAspectRatio) {
        // Height-constrained
        displayHeight = canvas.height * 0.9;
        displayWidth = displayHeight / dataAspectRatio;
    } else {
        // Width-constrained
        displayWidth = canvas.width * 0.9;
        displayHeight = displayWidth * dataAspectRatio;
    }
    
    // Center the image
    const offsetX = (canvas.width - displayWidth) / 2;
    const offsetY = (canvas.height - displayHeight) / 2;
    
    // Apply transforms
    ctx.translate(canvas.width/2 + state.panX, canvas.height/2 + state.panY);
    ctx.scale(state.zoom, state.zoom);
    ctx.translate(-canvas.width/2, -canvas.height/2);
    
    // Create temporary canvas for the actual data
    const tempCanvas = document.createElement('canvas');
    tempCanvas.width = width;
    tempCanvas.height = height;
    const tempCtx = tempCanvas.getContext('2d');
    
    const imageData = tempCtx.createImageData(width, height);
    const data = imageData.data;
    
    const windowWidth = window.simpleViewerData.windowWidth;
    const windowLevel = window.simpleViewerData.windowLevel;
    const windowMin = windowLevel - windowWidth / 2;
    const windowMax = windowLevel + windowWidth / 2;
    
    // Extract coronal slice - correct orientation
    for (let z = 0; z < volume.depth; z++) {
        const sliceData = volume.data[z];
        if (!sliceData) continue;
        
        for (let x = 0; x < volume.width; x++) {
            const srcIdx = sliceY * volume.width + x;
            // Correct orientation: flip vertically
            const dstIdx = ((height - 1 - z) * width + x) * 4;
            
            if (srcIdx < sliceData.length) {
                const hu = sliceData[srcIdx] * volume.slope + volume.intercept;
                let gray = ((hu - windowMin) / windowWidth) * 255;
                gray = Math.max(0, Math.min(255, gray));
                
                data[dstIdx] = gray;
                data[dstIdx + 1] = gray;
                data[dstIdx + 2] = gray;
                data[dstIdx + 3] = 255;
            }
        }
    }
    
    tempCtx.putImageData(imageData, 0, 0);
    
    // Draw the temp canvas to the main canvas with proper scaling
    ctx.drawImage(tempCanvas, offsetX, offsetY, displayWidth, displayHeight);
    
    // Draw ROI overlay on coronal view with display parameters before restoring so pan/zoom apply
    window.viewGeom = window.viewGeom || {};
    window.viewGeom.coronal = {
        offsetX, offsetY, displayWidth, displayHeight,
        dataWidth: width, dataHeight: height,
        canvasWidth: canvas.width, canvasHeight: canvas.height,
        panX: state.panX, panY: state.panY, zoom: state.zoom
    };
    const displayParams = {
        offsetX: offsetX,
        offsetY: offsetY,
        displayWidth: displayWidth,
        displayHeight: displayHeight,
        dataWidth: width,
        dataHeight: height
    };
    drawROIOverlayCoronal(ctx, volume, sliceY, displayParams);
    // Crosshair: vertical at sagittal X, horizontal at axial Z
    drawCrosshairCoronal(ctx, displayParams, volume);
    
    // Restore after overlay so transforms affect both
    ctx.restore();
    
    // Update info
    const infoElement = document.getElementById('info-coronal');
    if (infoElement) {
        const sliceNum = sliceY + 1;
        const totalSlices = volume.height;
        infoElement.innerHTML = `<span>Slice: <span id="coronal-slice">${sliceNum}/${totalSlices}</span></span><br>
                                 <span>WL: <span id="coronal-wl">${windowWidth}/${windowLevel}</span></span>`;
    }
}

function renderPlaceholderViews() {
    // Render sagittal view placeholder
    const sagCanvas = document.getElementById('viewport-sagittal');
    if (sagCanvas) {
        if (!sagCanvas.width) sagCanvas.width = 256;
        if (!sagCanvas.height) sagCanvas.height = 256;
        const ctx = sagCanvas.getContext('2d');
        ctx.fillStyle = '#1a1a1a';
        ctx.fillRect(0, 0, sagCanvas.width, sagCanvas.height);
        ctx.fillStyle = '#009999';
        ctx.font = '14px Inter';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText('Sagittal View', sagCanvas.width/2, sagCanvas.height/2);
        ctx.fillStyle = '#808080';
        ctx.font = '11px Inter';
        ctx.fillText('(Loading...)', sagCanvas.width/2, sagCanvas.height/2 + 20);
    }
    
    // Render coronal view placeholder
    const corCanvas = document.getElementById('viewport-coronal');
    if (corCanvas) {
        if (!corCanvas.width) corCanvas.width = 256;
        if (!corCanvas.height) corCanvas.height = 256;
        const ctx = corCanvas.getContext('2d');
        ctx.fillStyle = '#1a1a1a';
        ctx.fillRect(0, 0, corCanvas.width, corCanvas.height);
        ctx.fillStyle = '#009999';
        ctx.font = '14px Inter';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText('Coronal View', corCanvas.width/2, corCanvas.height/2);
        ctx.fillStyle = '#808080';
        ctx.font = '11px Inter';
        ctx.fillText('(Loading...)', corCanvas.width/2, corCanvas.height/2 + 20);
    }
    
    // Update info panels
    const infoSag = document.getElementById('info-sagittal');
    if (infoSag) {
        infoSag.innerHTML = `Sagittal<br>MPR View`;
    }
    
    const infoCor = document.getElementById('info-coronal');
    if (infoCor) {
        infoCor.innerHTML = `Coronal<br>MPR View`;
    }
    
    // 3D info element not present in current layout; skip.
}


// Viewer control functions
function toggleViewMode() {
    const isChecked = document.getElementById('toggleBurnedView').checked;
    
    if (dicomViewer && dicomViewer.toggleVolume) {
        dicomViewer.toggleVolume();
    } else if (window.simpleViewerData) {
        window.simpleViewerData.isShowingBurned = isChecked;
        displaySimpleViewer();
    }
}

function setWindowPreset(preset) {
    const presets = {
        'Soft Tissue': { window: 400, level: 40 },
        'Lung': { window: 1500, level: -600 },
        'Bone': { window: 1500, level: 300 },
        'Brain': { window: 80, level: 40 }
    };
    const target = presets[preset];
    if (!target) return;

    const targetModality = (activeTab === 'mr' && mrPreviewActive) ? 'MR' : 'CT';
    setWindowRangeFromWWL(target.window, target.level, targetModality);

    if (dicomViewer && dicomViewer.setWindowPreset) {
        dicomViewer.setWindowPreset(preset);
    } else if (window.simpleViewerData) {
        window.simpleViewerData.windowWidth = target.window;
        window.simpleViewerData.windowLevel = target.level;
        displaySimpleViewer();
    }

    // Optional: update any preset buttons if present
    const presetButtons = document.querySelectorAll('.window-presets .preset-btn');
    if (presetButtons && presetButtons.length) {
        presetButtons.forEach(btn => btn.classList.remove('active'));
        // No reliable event target here; callers should manage active state
    }
    applyWindowForActiveTab();
}

function updateWindowLevel() {
    // Legacy hook; inputs removed. Kept for safety if called programmatically.
    const targetModality = (activeTab === 'mr' && mrPreviewActive) ? 'MR' : 'CT';
    const range = targetModality === 'MR' ? mrWindowRange : ctWindowRange;
    const ww = Math.max(1, (range.max || 0) - (range.min || 0));
    const wl = ((range.max || 0) + (range.min || 0)) / 2;
    setWindowRangeFromWWL(ww, wl, targetModality);
    applyWindowForActiveTab();
    displaySimpleViewer();
}

function getDisplayWindowRange() {
    // Display windowing follows CT range only; MR uses its own clamp internally
    return ctWindowRange;
}

function syncWindowInputsToActiveTab() {
    const wwInput = document.getElementById('windowWidth');
    const wlInput = document.getElementById('windowLevel');
    const range = getDisplayWindowRange();
    const ww = Math.max(1, (range.max || 0) - (range.min || 0));
    const wl = ((range.max || 0) + (range.min || 0)) / 2;
    if (wwInput) wwInput.value = Math.round(ww);
    if (wlInput) wlInput.value = Math.round(wl);
    updateWindowRangeLabels();
}

function applyWindowForActiveTab() {
    const range = getDisplayWindowRange();
    const ww = Math.max(1, (range.max || 0) - (range.min || 0));
    const wl = ((range.max || 0) + (range.min || 0)) / 2;
    if (window.simpleViewerData) {
        window.simpleViewerData.windowWidth = ww;
        window.simpleViewerData.windowLevel = wl;
    }
    const wwInput = document.getElementById('windowWidth');
    const wlInput = document.getElementById('windowLevel');
    if (wwInput) wwInput.value = Math.round(ww);
    if (wlInput) wlInput.value = Math.round(wl);
    updateWindowRangeLabels();
}

function setWindowRangeFromWWL(ww, wl, modality = 'CT') {
    const min = wl - ww / 2;
    const max = wl + ww / 2;
    if (modality === 'MR') {
        mrWindowRange = { min, max };
    } else {
        ctWindowRange = { min, max };
    }
    updateWindowRangeLabels();
}

function updateWindowRangeLabels() {
    const ctLabel = document.getElementById('ctWindowLabel');
    if (ctLabel) ctLabel.textContent = `${Math.round(ctWindowRange.min)} to ${Math.round(ctWindowRange.max)}`;
    const mrLabel = document.getElementById('mrWindowLabel');
    if (mrLabel) mrLabel.textContent = `${Math.round(mrWindowRange.min)} to ${Math.round(mrWindowRange.max)}`;
    const ctMin = document.getElementById('ctWindowMin');
    const ctMax = document.getElementById('ctWindowMax');
    if (ctMin && ctMax) {
        ctMin.value = Math.round(ctWindowRange.min);
        ctMax.value = Math.round(ctWindowRange.max);
        updateDualRangeFill('ct');
    }
    const mrMin = document.getElementById('mrWindowMin');
    const mrMax = document.getElementById('mrWindowMax');
    if (mrMin && mrMax) {
        mrMin.value = Math.round(mrWindowRange.min);
        mrMax.value = Math.round(mrWindowRange.max);
        updateDualRangeFill('mr');
    }
}

function updateDualRangeFill(prefix) {
    const minEl = document.getElementById(`${prefix}WindowMin`);
    const maxEl = document.getElementById(`${prefix}WindowMax`);
    const container = document.getElementById(`${prefix}WindowContainer`);
    if (!minEl || !maxEl || !container) return;
    const minVal = parseFloat(minEl.value);
    const maxVal = parseFloat(maxEl.value);
    const minBound = parseFloat(minEl.min);
    const maxBound = parseFloat(minEl.max);
    const range = maxBound - minBound;
    if (!Number.isFinite(range) || range <= 0) return;
    const start = ((Math.min(minVal, maxVal) - minBound) / range) * 100;
    const end = ((Math.max(minVal, maxVal) - minBound) / range) * 100;
    const trackColor = '#777777';
    const bgColor = '#ffffff';
    const grad = `linear-gradient(to right, ${bgColor} 0%, ${bgColor} ${start}%, ${trackColor} ${start}%, ${trackColor} ${end}%, ${bgColor} ${end}%, ${bgColor} 100%)`;
    container.style.background = grad;
    minEl.style.background = 'transparent';
    maxEl.style.background = 'transparent';
}

function parseWindowFromDataset(ds) {
    if (!ds) return null;
    try {
        const wwRaw = ds.string?.(Tag.WindowWidth);
        const wlRaw = ds.string?.(Tag.WindowCenter);
        const ww = wwRaw ? parseFloat(String(wwRaw).split('\\')[0]) : null;
        const wl = wlRaw ? parseFloat(String(wlRaw).split('\\')[0]) : null;
        if (Number.isFinite(ww) && Number.isFinite(wl)) return { width: ww, center: wl };
    } catch (e) { /* ignore */ }
    return null;
}

function setDefaultCTWindow(ds) {
    const parsed = parseWindowFromDataset(ds);
    const ww = parsed?.width || 400;
    const wl = parsed?.center || 40;
    const min = wl - ww / 2;
    const max = wl + ww / 2;
    ctDefaultWindowRange = { min, max };
    ctWindowRange = { min, max };
    updateWindowRangeLabels();
    applyWindowForActiveTab();
    if (window.simpleViewerData) displaySimpleViewer();
}

function enableRangeDrag(prefix) {
    const container = document.getElementById(`${prefix}WindowContainer`);
    const minEl = document.getElementById(`${prefix}WindowMin`);
    const maxEl = document.getElementById(`${prefix}WindowMax`);
    if (!container || !minEl || !maxEl) return;

    let dragging = false;
    let startX = 0;
    let startMin = 0;
    let startMax = 0;

    const onMouseDown = (e) => {
        if (e.target !== container) return; // only drag when grabbing the track (grey bar)
        dragging = true;
        startX = e.clientX;
        startMin = parseFloat(minEl.value);
        startMax = parseFloat(maxEl.value);
        window.addEventListener('mousemove', onMouseMove);
        window.addEventListener('mouseup', onMouseUp);
        e.preventDefault();
    };
    const onMouseMove = (e) => {
        if (!dragging) return;
        const range = parseFloat(minEl.max) - parseFloat(minEl.min);
        if (!Number.isFinite(range) || range <= 0) return;
        const rect = container.getBoundingClientRect();
        const deltaPx = e.clientX - startX;
        const deltaVal = (deltaPx / rect.width) * range;
        const width = startMax - startMin;
        let newMin = startMin + deltaVal;
        let newMax = startMax + deltaVal;
        const minBound = parseFloat(minEl.min);
        const maxBound = parseFloat(minEl.max);
        if (newMin < minBound) {
            newMin = minBound;
            newMax = newMin + width;
        }
        if (newMax > maxBound) {
            newMax = maxBound;
            newMin = newMax - width;
        }
        minEl.value = newMin;
        maxEl.value = newMax;
        if (prefix === 'ct') {
            ctWindowRange = { min: newMin, max: newMax };
        } else {
            mrWindowRange = { min: newMin, max: newMax };
        }
        updateWindowRangeLabels();
        applyWindowForActiveTab();
        displaySimpleViewer();
    };
    const onMouseUp = () => {
        dragging = false;
        window.removeEventListener('mousemove', onMouseMove);
        window.removeEventListener('mouseup', onMouseUp);
    };

    container.addEventListener('mousedown', onMouseDown);
}

function setDefaultMRWindow(stats, ds) {
    // Prefer explicit MR window center/width if provided
    const parsed = parseWindowFromDataset(ds);
    if (parsed && Number.isFinite(parsed.width) && Number.isFinite(parsed.center)) {
        const min = parsed.center - parsed.width / 2;
        const max = parsed.center + parsed.width / 2;
        mrWindowRange = { min, max };
        mrDefaultWindowRange = { min, max };
        updateWindowRangeLabels();
        if (activeTab === 'mr') applyWindowForActiveTab();
        return;
    }
    if (!stats) return;
    // Fallback: typical MR viewing using percentiles
    const min = Number.isFinite(stats.min) ? stats.min : -500;
    const max = Number.isFinite(stats.p99) ? stats.p99 : (Number.isFinite(stats.p95) ? stats.p95 : min + 1000);
    mrWindowRange = { min, max };
    mrDefaultWindowRange = { min, max };
    updateWindowRangeLabels();
    if (activeTab === 'mr') {
        applyWindowForActiveTab();
    }
}

// Initialize dual-range drag once DOM is ready
setTimeout(() => {
    enableRangeDrag('ct');
    enableRangeDrag('mr');
    updateDualRangeFill('ct');
    updateDualRangeFill('mr');
}, 100);

function resetCtWindow() {
    const range = ctDefaultWindowRange || ctWindowRange;
    if (range) {
        ctWindowRange = { ...range };
        updateWindowRangeLabels();
        applyWindowForActiveTab();
        displaySimpleViewer();
    }
}

function resetMrWindow() {
    const range = mrDefaultWindowRange || mrWindowRange;
    if (range) {
        mrWindowRange = { ...range };
        updateWindowRangeLabels();
        applyWindowForActiveTab();
        displaySimpleViewer();
        if (mrPreviewActive) setTimeout(() => { buildMRPreview(false); }, 0);
    }
}

function onCtWindowRangeChange(which) {
    const minEl = document.getElementById('ctWindowMin');
    const maxEl = document.getElementById('ctWindowMax');
    if (!minEl || !maxEl) return;
    let minVal = which === 'min' ? parseInt(minEl.value) : ctWindowRange.min;
    let maxVal = which === 'max' ? parseInt(maxEl.value) : ctWindowRange.max;
    if (!Number.isFinite(minVal)) minVal = ctWindowRange.min;
    if (!Number.isFinite(maxVal)) maxVal = ctWindowRange.max;
    if (minVal >= maxVal) {
        minVal = maxVal - 1;
    }
    ctWindowRange = { min: minVal, max: maxVal };
    syncWindowInputsToActiveTab();
    const displayingCT = !(activeTab === 'mr' && mrPreviewActive);
    if (displayingCT) applyWindowForActiveTab();
    displaySimpleViewer();
    updateDualRangeFill('ct');
}

function onMrWindowRangeChange(which) {
    const minEl = document.getElementById('mrWindowMin');
    const maxEl = document.getElementById('mrWindowMax');
    if (!minEl || !maxEl) return;
    let minVal = which === 'min' ? parseInt(minEl.value) : mrWindowRange.min;
    let maxVal = which === 'max' ? parseInt(maxEl.value) : mrWindowRange.max;
    if (!Number.isFinite(minVal)) minVal = mrWindowRange.min;
    if (!Number.isFinite(maxVal)) maxVal = mrWindowRange.max;
    if (minVal >= maxVal) {
        minVal = maxVal - 1;
    }
    mrWindowRange = { min: minVal, max: maxVal };
    syncWindowInputsToActiveTab();
    // No display impact; MR window only clamps resample if used elsewhere
}

function navigateToSlice(value) {
    const slice = parseInt(value);
    
    if (window.simpleViewerData) {
        window.simpleViewerData.currentSlice = slice;
        displaySimpleViewer();
    }
}

function toggleROIVisibility(roiName) {
    if (dicomViewer && dicomViewer.toggleROIVisibility) {
        dicomViewer.toggleROIVisibility(roiName);
    }
}

function setActiveTool(toolName) {
    // Update active button
    document.querySelectorAll('.sidebar-panel .preset-btn').forEach(btn => {
        if (btn.id && btn.id.startsWith('tool-')) {
            btn.classList.remove('active');
        }
    });
    document.getElementById('tool-' + toolName.toLowerCase()).classList.add('active');
    
    if (dicomViewer && dicomViewer.setActiveTool) {
        dicomViewer.setActiveTool(toolName);
    }
}

function resetAllViews() {
    if (dicomViewer && dicomViewer.resetView) {
        Object.values(dicomViewer.viewportIds).forEach(viewportId => {
            dicomViewer.resetView(viewportId);
        });
    } else if (window.simpleViewerData) {
        const len = getActiveSeries().length || 1;
        window.simpleViewerData.currentSlice = Math.floor(len / 2);
        window.simpleViewerData.windowWidth = 400;
        window.simpleViewerData.windowLevel = 40;
        displaySimpleViewer();
    }
}

function closeViewer() {
    // No longer needed with single interface
    // Viewer is always visible
}

function cancelExport() {
    closeViewer();
}

async function confirmExport() {
    // Close viewer
    closeViewer();
    
    // Proceed with download
    if (window.processedCTsForExport) {
        const zip = new window.JSZip();
        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').slice(0, -5);
        
        // Create folder name with ROI names and HU values
        const selectedROIs = [];
        document.querySelectorAll('.burn-in-item').forEach(item => {
            const checkbox = item.querySelector('.burn-in-checkbox');
            if (checkbox && checkbox.checked) {
                const roiName = item.querySelector('.burn-in-name').textContent;
                const huValue = item.querySelector('.hu-input').value;
                selectedROIs.push(`${roiName}_${huValue}HU`);
            }
        });
        
        const roiSuffix = selectedROIs.length > 0 ? `_${selectedROIs.slice(0, 3).join('_')}` : '';
        const folderName = `ROIOverride${roiSuffix}_${timestamp}`;
        
        for (const processedCT of window.processedCTsForExport) {
            // Use the modified byte array directly
            const arrayBuffer = processedCT.byteArray.buffer;
            zip.file(`${folderName}/${processedCT.filename}`, arrayBuffer);
        }
        
        // Generate and download zip
        zip.generateAsync({ type: 'blob' }).then(function(content) {
            const a = document.createElement('a');
            a.href = URL.createObjectURL(content);
            a.download = `${folderName}.zip`;
            a.click();
            
            showMessage('success', 'Burn-in complete! Files are being downloaded.');
            updateStatus('Process completed successfully');
        });
    }
}

function updateStatus(message) {
    const progressText = document.getElementById('progressText');
    if (progressText) {
        progressText.textContent = message;
    }
}

function updateProgress(percent) {
    document.getElementById('progressFill').style.width = percent + '%';
}

// Add missing BlueLight helper functions
function getByid(id) {
    return document.getElementById(id);
}

// Generate unique UID
function generateUID() {
    const prefix = '2.25.';
    let uid = prefix;
    for (let i = 0; i < 36; i++) {
        uid += Math.floor(Math.random() * 10);
    }
    return uid;
}

function showMessage(type, message) {
    const messageDiv = document.getElementById('statusMessage');
    messageDiv.className = 'status-message ' + type;
    messageDiv.textContent = message;
    
    setTimeout(() => {
        messageDiv.className = 'status-message';
    }, 5000);
}
function rebuildMrBlend() {
    if (!mrResampledSlices || !mrResampledSlices.length || !ctFiles || !ctFiles.length) return mrResampledSlices || [];
    const blended = [];
    const blend = mrBlendFraction;
    for (let i = 0; i < mrResampledSlices.length; i++) {
        const mrSlice = mrResampledSlices[i];
        const ctSlice = ctFiles[i];
        const ds = ctSlice?.dataSet;
        const pixelDataElement = ds?.elements?.x7fe00010;
        if (!pixelDataElement || !mrSlice.huData) {
            blended.push(mrSlice);
            continue;
        }
        let ctPixels = null;
        try {
            ctPixels = new Int16Array(ctSlice.byteArray.buffer, pixelDataElement.dataOffset, pixelDataElement.length / 2);
        } catch (e) {
            blended.push(mrSlice);
            continue;
        }
        const slope = ds.floatString(Tag.RescaleSlope) || 1;
        const intercept = ds.floatString(Tag.RescaleIntercept) || 0;
        const outHU = new Float32Array(ctPixels.length);
        for (let px = 0; px < ctPixels.length; px++) {
            const ctHU = ctPixels[px] * slope + intercept;
            const mrHU = mrSlice.huData[px];
            const fused = (1 - blend) * ctHU + blend * mrHU;
            outHU[px] = Math.max(-1200, Math.min(2000, fused));
        }
        const modifiedPixelData = new Int16Array(outHU.length);
        for (let px = 0; px < outHU.length; px++) {
            modifiedPixelData[px] = Math.max(-32768, Math.min(32767, Math.round((outHU[px] - intercept) / slope)));
        }
        blended.push({ ...mrSlice, modifiedPixelData, huData: outHU });
    }
    mrBlendedSlices = blended;
    return blended;
}
