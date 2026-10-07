(() => {
  'use strict';
  const data = JSON.parse(document.getElementById('proof-data').textContent);
  const $ = id => document.getElementById(id);
  const number = n => n.toLocaleString('en-US');
  const node = (tag, text, className) => {
    const element = document.createElement(tag);
    if (text != null) element.textContent = text;
    if (className) element.className = className;
    return element;
  };
  const url = path => data.repository + '/blob/' + data.branch + '/' + path.split('/').map(encodeURIComponent).join('/').replace(/%23/g, '#');
  const external = (label, path, className) => {
    const a = node('a', label, className);
    a.href = url(path); a.target = '_blank'; a.rel = 'noopener noreferrer';
    return a;
  };
  document.querySelectorAll('[data-repo-path]').forEach(a => {
    a.href = url(a.dataset.repoPath); a.target = '_blank'; a.rel = 'noopener noreferrer';
  });
  const modules = data.modules.map(([path, lib, topic, orbits]) => ({
    id: 'module:' + path, kind:'module', title:path.split('/').pop().replace(/\.lean$/, ''),
    paths:[path], libraries:[data.libraries[lib]], topic:data.topics[topic], orbits,
    generated:data.topics[topic] === 'Generated certificates',
    search:(path + ' ' + path.replace(/\.lean$/,'').replaceAll('/','.') + ' ' + data.topics[topic] + ' ' + data.libraries[lib]).toLowerCase()
  }));
  const byPath = new Map(modules.map(m => [m.paths[0], m]));
  const guides = data.guides.map(g => ({...g,kind:'guide',topic:g.section,generated:false,
    libraries:[...new Set(g.paths.map(p => byPath.get(p).libraries[0]))],
    search:(g.title + ' ' + g.section + ' ' + g.paths.map(p=>byPath.get(p).search).join(' ')).toLowerCase()}));
  const priority = ['MainTheory/Orbit2FullImage.lean','MainTheory/Orbit3FullImage.lean','QECC/FirstTheorem.lean','QECC/SecondTheorem.lean'];
  guides.sort((a,b) => {
    const rank = row => {const i = priority.indexOf(row.paths[0]); return i < 0 ? priority.length : i;};
    return rank(a) - rank(b);
  });
  const all = new Map([...guides,...modules].map(r => [r.id,r]));
  const orbitOptions = [...new Set([...guides,...modules].flatMap(r => r.orbits))].sort((a,b) => a-b);
  const defaults = {mode:'guides',q:'',library:'',topic:'',orbit:'',generated:false,selected:guides.find(g => g.paths.includes(data.default_selected_path)).id};
  let state = {...defaults}, pageLimit = 24, filtered = [], lastFocus = null;

  function readHash() {
    const p = new URLSearchParams(location.hash.slice(1));
    state = {...defaults};
    if (p.get('mode') === 'modules') state.mode = 'modules';
    state.q = p.get('q') || '';
    if (data.libraries.includes(p.get('library'))) state.library = p.get('library');
    state.topic = p.get('topic') || '';
    if (orbitOptions.includes(Number(p.get('orbit')))) state.orbit = p.get('orbit');
    state.generated = p.get('generated') === '1';
    if (all.has(p.get('selected'))) state.selected = p.get('selected');
  }
  function writeHash() {
    const p = new URLSearchParams();
    for (const key of ['mode','q','library','topic','orbit','selected']) {
      if (state[key] && (key !== 'mode' || state.mode !== 'guides')) p.set(key,state[key]);
    }
    if (state.generated) p.set('generated','1');
    history.replaceState(null,'','#' + p.toString());
  }
  function queryParts(query) {
    const exact = [];
    const words = query.toLowerCase().replace(/(?:^|\s)orbits?\s*(\d+)(?=\s|$)/g, (_, n) => {exact.push(Number(n));return ' ';}).trim().split(/\s+/).filter(Boolean);
    return {exact,words};
  }
  function filterRows(rows, options) {
    const q = queryParts(options.q || '');
    return rows.filter(r => (!options.library || r.libraries.includes(options.library)) &&
      (!options.topic || r.topic === options.topic) && (!options.orbit || r.orbits.includes(Number(options.orbit))) &&
      (options.mode !== 'modules' || options.generated || !r.generated) &&
      q.exact.every(n => r.orbits.includes(n)) && q.words.every(w => r.search.includes(w)));
  }
  function toast(text) { $('toast').textContent = text; $('toast').hidden = false; setTimeout(() => {$('toast').hidden=true;},2600); }
  async function copy(text) {
    try { await navigator.clipboard.writeText(text); toast('Copied to clipboard'); }
    catch { toast('Clipboard unavailable. Select and copy the displayed name.'); }
  }
  function option(value,label) {const o=node('option',label);o.value=value;return o;}
  $('library-select').append(option('','All libraries'));
  data.libraries.forEach(lib => $('library-select').append(option(lib,lib)));
  $('orbit-select').append(option('','All orbits'));
  orbitOptions.forEach(n => $('orbit-select').append(option(String(n),'Orbit ' + n)));
  $('sidebar-count').textContent=number(data.status.active_lean_modules);
  $('module-count').textContent=number(data.status.active_lean_modules);
  $('axiom-count').textContent=number(data.status.axiom_roots);
  $('held-count').textContent=data.status.held_main_issues;
  $('version-label').textContent=data.status.paper_version;
  const siComplete=data.status.si_fully_kernel_correspondence==='complete';
  $('review-summary').textContent='Recorded SI correspondence is '+(siComplete?'complete':'incomplete')+' for '+data.status.paper_version+'; later manuscript revisions need a separate review.';
  $('held-caption').textContent=data.status.held_main_issues ? 'combined review incomplete' : 'see version-specific review';
  $('guide-total').textContent=guides.length;
  $('catalog-total').textContent=number(modules.length);
  $('source-binding').textContent='Source catalog SHA-256 · ' + data.source_hashes_lf['results/proof-modules.json'].slice(0,16) + '…';

  function buildLibraries() {
    $('library-buttons').replaceChildren();
    for (const lib of ['',...data.libraries]) {
      const button=node('button',lib || 'All libraries','library-button');
      button.type='button';button.dataset.library=lib;
      button.append(node('span',number(lib ? data.library_counts[lib] : modules.length)));
      button.addEventListener('click',() => {state.library=lib;pageLimit=24;render();});
      $('library-buttons').append(button);
    }
  }
  function tags(row) {
    const wrap=node('div',null,'card-tags');
    row.libraries.slice(0,2).forEach(lib=>wrap.append(node('span',lib,'pill')));
    row.orbits.slice(0,3).forEach(n=>wrap.append(node('span','Orbit '+n,'pill orbit')));
    if (row.generated) wrap.append(node('span','Generated','pill generated'));
    return wrap;
  }
  function card(row) {
    const button=node('button',null,'proof-card' + (row.id===state.selected ? ' selected' : ''));
    button.type='button';button.dataset.record=row.id;button.setAttribute('aria-pressed',String(row.id===state.selected));
    button.append(node('div',row.kind==='guide' ? row.section : 'Source module','card-kicker'));
    button.append(node('h3',row.title),node('span','›','card-chevron'));
    button.append(node('div',row.kind==='guide' ? row.paths.length + (row.paths.length===1 ? ' source entry' : ' source entries') : row.topic,'card-meta'));
    button.append(tags(row));
    button.addEventListener('click',()=>{
      state.selected=row.id;render();
      const replacement=document.querySelector('[data-record="'+CSS.escape(row.id)+'"]');
      replacement?.focus({preventScroll:true});
      if (matchMedia('(max-width:1000px)').matches) {
        lastFocus=replacement; $('dialog-content').replaceChildren(detailContent(row));
        $('detail-dialog').showModal();
      }
    });
    return button;
  }
  function linkList(title,resources) {
    const section=node('section',null,'detail-section');section.append(node('h3',title));
    const list=node('div',null,'detail-links');
    resources.forEach(([label,path])=>{const a=external(label,path);a.append(node('span','↗','external'));list.append(a);});
    section.append(list);return section;
  }
  function detailContent(row) {
    const fragment=document.createDocumentFragment(), inner=node('div',null,'detail-inner');
    inner.append(node('div',row.kind==='guide' ? 'SELECTED PROOF GUIDE' : 'SOURCE CATALOG ENTRY','detail-eyebrow'));
    inner.append(node('h2',row.title),tags(row));
    const endpoint=data.endpoints[row.paths[0]];
    const intro=endpoint ? 'Converse and interval attainment for actual full-KL encoders. This is a recorded full-image endpoint.' :
      (row.kind==='guide' ? 'A curated entry from the paper-facing proof index. Read its hypotheses and conclusion, then follow the supporting imports.' :
       'An active Lean source module. Its topic and orbit tags help navigation; they do not assign manuscript coverage.');
    inner.append(node('p',intro,'detail-summary'));
    inner.append(external('Open primary Lean source ↗',row.paths[0],'source-link'));
    const name=endpoint ? endpoint.declaration : row.paths[0].replace(/\.lean$/,'').replaceAll('/','.');
    const nameSection=node('section',null,'detail-section');
    nameSection.append(node('h3',endpoint ? 'Theorem endpoint' : 'Module name'),node('div',name,'endpoint'));
    const copyButton=node('button','Copy name','copy-button');copyButton.type='button';copyButton.addEventListener('click',()=>copy(name));
    nameSection.append(copyButton);inner.append(nameSection);
    if(row.paths.length>1) inner.append(linkList('Supporting entry modules',row.paths.slice(1).map(p=>[p.split('/').pop().replace(/\.lean$/,''),p])));
    if(endpoint) inner.append(linkList('Exact certificate resources',endpoint.resources));
    inner.append(linkList('Recorded acceptance & review',data.evidence));
    const scope=node('div',null,'detail-scope');
    scope.append(node('strong','Scope · ' + data.status.paper_version));
    const held=data.status.held_main_issues;
    const open=data.status.open_enumerator_images;
    scope.append(node('div','SI correspondence is '+(siComplete?'complete':'incomplete')+' for this snapshot. '+
      (held ? held+' held main-text issues prevent complete combined manuscript certification.' : 'No held main-text issues are recorded.')+
      (open.length ? ' Orbit-'+open.join('/')+' full enumerator images remain open.' : '')));
    inner.append(scope);fragment.append(inner);
    const footer=node('div','Follow the source, then check its hypotheses and recorded evidence.','detail-footer');
    fragment.append(footer);return fragment;
  }
  function render() {
    const rows=state.mode==='guides' ? guides : modules;
    const topics=[...new Set(rows.map(r=>r.topic))].sort();
    if(state.topic && !topics.includes(state.topic)) state.topic='';
    $('topic-select').replaceChildren(option('','All topics'),...topics.map(t=>option(t,t)));
    filtered=filterRows(rows,state);
    if(!filtered.some(r=>r.id===state.selected)) state.selected=filtered[0]?.id || '';
    $('guides-tab').classList.toggle('active',state.mode==='guides');
    $('modules-tab').classList.toggle('active',state.mode==='modules');
    $('guides-tab').setAttribute('aria-selected',String(state.mode==='guides'));
    $('modules-tab').setAttribute('aria-selected',String(state.mode==='modules'));
    $('guides-tab').tabIndex=state.mode==='guides' ? 0 : -1;
    $('modules-tab').tabIndex=state.mode==='modules' ? 0 : -1;
    $('results').setAttribute('aria-labelledby',state.mode+'-tab');
    $('search').value=state.q;$('topic-select').value=state.topic;$('orbit-select').value=state.orbit;
    $('library-select').value=state.library;$('generated').checked=state.generated;
    $('generated-control').hidden=state.mode!=='modules';
    document.querySelectorAll('.library-button').forEach(b=>{b.classList.toggle('active',b.dataset.library===state.library);b.setAttribute('aria-pressed',String(b.dataset.library===state.library));});
    const mode=state.mode==='guides' ? 'proof guides' : 'modules';
    $('result-count').textContent=number(filtered.length)+' '+mode+' · '+number(Math.min(pageLimit,filtered.length))+' shown';
    $('mode-note').textContent=state.mode==='guides' ? 'Curated entries from the proof index' : (state.generated ? 'Complete active source catalog' : 'Generated certificate shards hidden');
    const visible=filtered.slice(0,pageLimit);
    $('results').replaceChildren(...visible.map(card));
    if(!filtered.length) {
      const empty=node('div',null,'empty');empty.append(node('strong','No matching proofs'),node('p','Try another keyword, clear an orbit or topic filter, or reset the search.'));
      $('results').append(empty);
    }
    $('load-more').hidden=filtered.length<=pageLimit;
    const selected=all.get(state.selected);
    $('detail').replaceChildren(selected ? detailContent(selected) : node('div','Select a proof to inspect its source and evidence.','detail-inner'));
    writeHash();
  }
  function setMode(mode) {state.mode=mode;state.topic='';pageLimit=24;render();}
  $('guides-tab').addEventListener('click',()=>setMode('guides'));
  $('modules-tab').addEventListener('click',()=>setMode('modules'));
  document.querySelector('.browse-tabs').addEventListener('keydown',e=>{
    if(['ArrowLeft','ArrowRight','Home','End'].includes(e.key)){
      e.preventDefault();const focused=document.activeElement.id==='guides-tab'?'guides':'modules';
      const mode=e.key==='Home'?'guides':e.key==='End'?'modules':focused==='guides'?'modules':'guides';
      setMode(mode);$(mode+'-tab').focus();
    }
  });
  $('search').addEventListener('input',e=>{state.q=e.target.value;pageLimit=24;render();});
  $('topic-select').addEventListener('change',e=>{state.topic=e.target.value;pageLimit=24;render();});
  $('orbit-select').addEventListener('change',e=>{state.orbit=e.target.value;pageLimit=24;render();});
  $('library-select').addEventListener('change',e=>{state.library=e.target.value;pageLimit=24;render();});
  $('generated').addEventListener('change',e=>{state.generated=e.target.checked;pageLimit=24;render();});
  $('reset').addEventListener('click',()=>{state={...defaults,mode:state.mode};pageLimit=24;render();});
  $('load-more').addEventListener('click',()=>{pageLimit+=24;render();});
  document.querySelector('.skip').addEventListener('click',e=>{e.preventDefault();$('search').focus();});
  $('close-dialog').addEventListener('click',()=>$('detail-dialog').close());
  $('detail-dialog').addEventListener('close',()=>{const replacement=document.querySelector('[data-record="'+CSS.escape(state.selected)+'"]');(replacement || lastFocus)?.focus();});
  addEventListener('hashchange',()=>{readHash();pageLimit=24;render();});
  addEventListener('keydown',e=>{if(e.key==='/'&&!['INPUT','SELECT','TEXTAREA'].includes(document.activeElement.tagName)){e.preventDefault();$('search').focus();}});
  function theme(value) {
    document.documentElement.dataset.theme=value;
    $('theme-toggle').setAttribute('aria-label','Switch to '+(value==='dark'?'light':'dark')+' theme');
    $('theme-toggle').textContent=value==='dark'?'☼':'☾';
    try{localStorage.setItem('sslp-explorer-theme',value);}catch{}
  }
  let preference='dark';try{preference=localStorage.getItem('sslp-explorer-theme')||'dark';}catch{}
  theme(preference==='light'?'light':'dark');
  $('theme-toggle').addEventListener('click',()=>theme(document.documentElement.dataset.theme==='dark'?'light':'dark'));
  buildLibraries();readHash();render();
  window.SSLPExplorer={counts:{guides:guides.length,modules:modules.length},getState:()=>({...state}),getResults:()=>filtered.map(r=>({id:r.id,paths:r.paths,orbits:r.orbits}))};
})();
