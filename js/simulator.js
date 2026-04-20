const examples = [
  { g: "S -> AB\nA -> a\nB -> b", s: "ab" },
  { g: "S -> AB | BC\nA -> BA | a\nB -> CC | b\nC -> AB | a", s: "baaba" },
  { g: "S -> aSb | ab", s: "aabb" },
  { g: "S -> AB | AC\nA -> a\nB -> BC\nC -> b", s: "aab" },
  { g: "S -> aS | bS | a | b", s: "aba" }
];

function loadExample(i) {
  document.getElementById('grammar-input').value = examples[i].g;
  document.getElementById('string-input').value = examples[i].s;
  resetAll();
}

let G = {}, startSym = 'S', n = 0, w = '';
let dp = [], steps = [], stepIdx = 0;
let isStepMode = false, animTimer = null, cellDetails = [];
let totalSteps = 0;

function parseGrammar(txt) {
  const g = {};
  let start = null;
  for (const line of txt.trim().split('\n')) {
    const m = line.match(/^\s*([A-Z])\s*->\s*(.*)$/);
    if (!m) continue;
    const lhs = m[1];
    if (!start) start = lhs;
    if (!g[lhs]) g[lhs] = [];
    for (let r of m[2].split('|').map(x => x.trim())) {
      if (!r) { g[lhs].push(''); continue; }
      r = r.replace(/\s+/g, '');
      if (r === 'e' || r === 'ε' || r === '^') r = '';
      g[lhs].push(r);
    }
  }
  return { g, start };
}

// ── Deep-clone a grammar (values are arrays of strings) ──────────────────────
function cloneG(g) {
  const c = {};
  for (const [k, v] of Object.entries(g)) c[k] = [...v];
  return c;
}

// ── Check strict CNF ──────────────────────────────────────────────────────────
function isCNF(g) {
  for (const rules of Object.values(g))
    for (const r of rules)
      if (!((r.length === 1 && /^[^A-Z]$/.test(r)) ||
            (r.length === 2 && /^[A-Z]{2}$/.test(r))))
        return false;
  return true;
}

// ── Full CNF conversion ───────────────────────────────────────────────────────
// Returns { g, start, log } where log is an array of { step, desc, grammar }
function convertToCNF(gIn, startIn) {
  let g = cloneG(gIn);
  let start = startIn;
  const log = [];

  // Reliable fresh single-character variable generator.
  // CYK relies on each character in a rule string being one symbol,
  // so ALL variable names MUST be exactly one uppercase letter.
  const usedVars = new Set(Object.keys(g));
  const UPPERS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
  function freshVar() {
    for (const ch of UPPERS) {
      if (!usedVars.has(ch)) { usedVars.add(ch); return ch; }
    }
    throw new Error('Ran out of single-letter variable names (grammar too large).');
  }

  function grammarText(g) {
    return Object.entries(g)
      .map(([A, rules]) => `${A} → ${[...new Set(rules)].join(' | ')}`)
      .join('\n');
  }

  // ── STEP 1: START ─────────────────────────────────────────────────────────
  const startOnRHS = Object.values(g).flat().some(r => {
    // Check every symbol in r for the start variable (each char is one symbol
    // only if grammar uses single-char variable names, which we enforce)
    return [...r].some(ch => ch === start);
  });
  if (startOnRHS) {
    const S0 = freshVar();
    g = { [S0]: [start], ...g };
    start = S0;
    log.push({
      step: 'START',
      desc: `Start symbol <b>${startIn}</b> appears on a RHS. Added new start <b>${S0} → ${startIn}</b>.`,
      grammar: grammarText(g)
    });
  } else {
    log.push({
      step: 'START',
      desc: `Start symbol <b>${start}</b> does not appear on any RHS — no change needed.`,
      grammar: grammarText(g)
    });
  }

  // ── STEP 2: DEL — eliminate ε-productions ────────────────────────────────
  function getNullable(g) {
    const nullable = new Set();
    let changed = true;
    while (changed) {
      changed = false;
      for (const [A, rules] of Object.entries(g)) {
        if (!nullable.has(A)) {
          if (rules.includes('') ||
              rules.some(r => r.length > 0 && [...r].every(ch => nullable.has(ch)))) {
            nullable.add(A); changed = true;
          }
        }
      }
    }
    return nullable;
  }
  const nullable = getNullable(g);
  if (nullable.size > 0) {
    const newG = {};
    for (const [A, rules] of Object.entries(g)) {
      const newRules = new Set();
      for (const r of rules) {
        if (r === '') continue;
        // Each character in r is a symbol (single-char variable or terminal).
        // Find positions of nullable symbols.
        const syms = [...r];
        const nullPos = syms.map((ch, i) => nullable.has(ch) ? i : -1).filter(x => x >= 0);
        const combos = 1 << nullPos.length;
        for (let mask = 0; mask < combos; mask++) {
          const built = syms.filter((_, ci) => {
            const posIdx = nullPos.indexOf(ci);
            return !(posIdx >= 0 && (mask >> posIdx) & 1);
          }).join('');
          if (built !== '') newRules.add(built);
        }
      }
      newG[A] = [...newRules];
    }
    g = newG;
    log.push({
      step: 'DEL (ε-rules)',
      desc: `Nullable variables: <b>{${[...nullable].join(', ')}}</b>. Added all non-empty combinations with nullable symbols optionally removed.`,
      grammar: grammarText(g)
    });
  } else {
    log.push({
      step: 'DEL (ε-rules)',
      desc: 'No ε-productions found — no change needed.',
      grammar: grammarText(g)
    });
  }

  // ── STEP 3: UNIT — eliminate unit productions A → B ──────────────────────
  function getUnitClosure(g, A) {
    const closure = new Set([A]);
    const queue = [A];
    while (queue.length) {
      const cur = queue.shift();
      for (const r of (g[cur] || [])) {
        if (r.length === 1 && /^[A-Z]$/.test(r) && !closure.has(r)) {
          closure.add(r); queue.push(r);
        }
      }
    }
    return closure;
  }
  let hadUnit = false;
  const newG2 = {};
  for (const A of Object.keys(g)) {
    const closure = getUnitClosure(g, A);
    const rules = new Set();
    for (const B of closure) {
      for (const r of (g[B] || [])) {
        // Keep only non-unit rules
        if (!(r.length === 1 && /^[A-Z]$/.test(r))) rules.add(r);
      }
    }
    newG2[A] = [...rules];
    if (closure.size > 1) hadUnit = true;
  }
  if (hadUnit) {
    g = newG2;
    log.push({
      step: 'UNIT (unit rules)',
      desc: 'Eliminated unit productions by replacing A → B with all non-unit rules reachable via the unit closure.',
      grammar: grammarText(g)
    });
  } else {
    log.push({
      step: 'UNIT (unit rules)',
      desc: 'No unit productions found — no change needed.',
      grammar: grammarText(g)
    });
  }

  // ── STEP 4: TERM — replace terminals mixed in long rules ─────────────────
  // Each rule is stored as a string; each character is one symbol (since all
  // variable names are single characters after parsing).
  // For rules of length ≥ 2 replace every terminal character with a new var.
  const termMap = {}; // terminal char → new variable name
  let hadTerm = false;
  const newG3 = {};
  // Copy existing rules first
  for (const [A, rules] of Object.entries(g)) newG3[A] = [...rules];

  for (const A of Object.keys(g)) {
    newG3[A] = g[A].map(r => {
      if (r.length <= 1) return r;
      return [...r].map(ch => {
        if (/^[^A-Z]$/.test(ch)) {
          if (!termMap[ch]) {
            const tv = freshVar();
            termMap[ch] = tv;
            newG3[tv] = [ch];
            hadTerm = true;
          }
          return termMap[ch];
        }
        return ch;
      }).join('');
    });
  }

  if (hadTerm) {
    g = newG3;
    log.push({
      step: 'TERM (terminals in long rules)',
      desc: `Replaced mixed terminals in rules of length ≥ 2 with new variables: <b>${Object.entries(termMap).map(([t,v]) => `${v}→${t}`).join(', ')}</b>.`,
      grammar: grammarText(g)
    });
  } else {
    log.push({
      step: 'TERM (terminals in long rules)',
      desc: 'No terminals found in multi-symbol rules — no change needed.',
      grammar: grammarText(g)
    });
  }

  // ── STEP 5: BIN — binarise rules of length > 2 ───────────────────────────
  // After TERM every symbol in every rule is either a terminal (length-1 rule)
  // or a single uppercase letter. So each CHARACTER in the rule string is one
  // symbol and r.length gives the rule length correctly.
  let hadBin = false;
  const newG4 = {};
  for (const A of Object.keys(g)) newG4[A] = [];
  const binMap = {}; // mapping string suffix -> new variable

  for (const [A, rules] of Object.entries(g)) {
    for (const r of rules) {
      if (r.length <= 2) {
        newG4[A].push(r);
      } else {
        hadBin = true;
        // r = X0 X1 X2 ... Xk  (each char is one symbol)
        // Produce: A → X0 N0, N0 → X1 N1, ..., N(k-2) → X(k-1) Xk
        // We reuse intermediate variables for matching suffixes to avoid redundant rules.
        const syms = [...r]; // array of single-char symbols
        let curLHS = A;
        for (let si = 0; si < syms.length - 2; si++) {
          const suffix = syms.slice(si + 1).join('');
          let newVar = binMap[suffix];
          let isNew = false;
          if (!newVar) {
            newVar = freshVar();
            binMap[suffix] = newVar;
            newG4[newVar] = [];
            isNew = true;
          }
          newG4[curLHS] = newG4[curLHS] || [];
          newG4[curLHS].push(syms[si] + newVar);
          curLHS = newVar;
          
          if (!isNew && newG4[newVar].length > 0) {
            curLHS = null;
            break;
          }
        }
        if (curLHS !== null) {
          newG4[curLHS] = newG4[curLHS] || [];
          newG4[curLHS].push(syms[syms.length - 2] + syms[syms.length - 1]);
        }
      }
    }
  }

  if (hadBin) {
    g = newG4;
    log.push({
      step: 'BIN (long rules)',
      desc: 'Binarised rules with > 2 symbols by introducing intermediate variables (N0, N1, …).',
      grammar: grammarText(g)
    });
  } else {
    log.push({
      step: 'BIN (long rules)',
      desc: 'No rules with more than 2 symbols — no change needed.',
      grammar: grammarText(g)
    });
  }

  return { g, start, log };
}

// ── Format grammar for display ────────────────────────────────────────────────
function grammarToText(g) {
  return Object.entries(g)
    .map(([A, rules]) => `${A} -> ${rules.join(' | ')}`)
    .join('\n');
}

function prepare() {
  const gtxt = document.getElementById('grammar-input').value;
  w = document.getElementById('string-input').value.trim();
  if (!w) { alert('Please enter an input string.'); return false; }
  const { g: gRaw, start: startRaw } = parseGrammar(gtxt);
  if (!startRaw) { alert('Invalid grammar. Use format: S -> AB | a'); return false; }

  const cnfPanel = document.getElementById('cnf-warn');

  if (!isCNF(gRaw)) {
    // Convert and show log
    const { g: gCNF, start: startCNF, log } = convertToCNF(gRaw, startRaw);
    G = gCNF; startSym = startCNF;

    let logHTML = `<div style="margin-bottom:8px;font-weight:600;color:#92400e">⚙ Grammar converted to CNF automatically</div>`;
    logHTML += `<div style="margin-bottom:10px;font-size:11px;color:#78350f">The original grammar was not in Chomsky Normal Form. The 5-step conversion was applied:</div>`;
    for (const entry of log) {
      logHTML += `<div class="cnf-step">
        <span class="cnf-step-label">${entry.step}</span>
        <span>${entry.desc}</span>
        <pre class="cnf-grammar">${entry.grammar}</pre>
      </div>`;
    }
    logHTML += `<div style="margin-top:10px;padding:8px 10px;background:#fef3c7;border-radius:6px;font-size:11px;color:#78350f">
      <b>Final CNF grammar used for CYK:</b><pre style="margin-top:4px;font-family:'DM Mono',monospace;font-size:11px;white-space:pre-wrap">${grammarToText(G)}</pre>
    </div>`;

    cnfPanel.style.display = 'block';
    cnfPanel.innerHTML = logHTML;
  } else {
    G = gRaw; startSym = startRaw;
    cnfPanel.style.display = 'block';
    cnfPanel.innerHTML = `<span style="color:#065f46;font-weight:500">✓ Grammar is already in CNF — no conversion needed.</span>`;
    cnfPanel.style.background = 'var(--green-light)';
    cnfPanel.style.borderColor = 'var(--green-border)';
    cnfPanel.style.color = '#065f46';
  }

  n = w.length;
  dp = Array.from({ length: n }, () => Array.from({ length: n }, () => new Set()));
  cellDetails = Array.from({ length: n }, () => Array(n).fill(null));

  const allRules = Object.values(G).flat().length;
  document.getElementById('stat-n').textContent = n;
  document.getElementById('stat-cells').textContent = Math.round(n * (n + 1) / 2);
  document.getElementById('stat-vars').textContent = Object.keys(G).length;
  document.getElementById('stat-rules').textContent = allRules;
  document.getElementById('stats-card').style.display = '';

  renderTable();
  document.getElementById('status-bar').style.display = 'none';
  document.getElementById('progress-wrap').style.display = '';
  document.getElementById('progress-bar').style.width = '0%';
  return true;
}

function buildSteps() {
  // Only store coordinates; splits/vars are computed lazily in applyStep
  // so that dp is already populated for shorter substrings when needed.
  steps = [];
  for (let i = 0; i < n; i++) {
    steps.push({ i, j: i, length: 1 });
  }
  for (let len = 2; len <= n; len++) {
    for (let i = 0; i <= n - len; i++) {
      steps.push({ i, j: i + len - 1, length: len });
    }
  }
  totalSteps = steps.length;
}

function applyStep(step) {
  const { i, j, length } = step;

  if (length === 1) {
    // Terminal rule: find all variables A -> w[i]
    const ch = w[i];
    const vars = [];
    for (const [A, rules] of Object.entries(G))
      if (rules.includes(ch)) vars.push(A);
    for (const v of vars) dp[i][j].add(v);
    cellDetails[i][j] = { vars: [...dp[i][j]], splits: [], ch, i, j, length, substr: ch };
  } else {
    // Binary rule: for each split point k, check A -> B C
    const splits = [], vars = new Set();
    for (let k = i; k < j; k++) {
      for (const [A, rules] of Object.entries(G)) {
        for (const r of rules) {
          if (r.length === 2) {
            const B = r[0], C = r[1];
            if (dp[i][k].has(B) && dp[k + 1][j].has(C)) {
              vars.add(A);
              splits.push({ k, A, B, C, left: w.slice(i, k + 1), right: w.slice(k + 1, j + 1) });
            }
          }
        }
      }
    }
    for (const v of vars) dp[i][j].add(v);
    cellDetails[i][j] = { vars: [...dp[i][j]], splits, ch: null, i, j, length, substr: w.slice(i, j + 1) };
  }

  const hadNew = dp[i][j].size > 0;
  const progress = ((stepIdx + 1) / totalSteps * 100).toFixed(0);
  document.getElementById('progress-bar').style.width = progress + '%';
  renderTable(i, j, hadNew);
  updateExplain(i, j, cellDetails[i][j]);
}

function animateSteps() {
  let idx = 0;
  function next() {
    if (idx >= steps.length) { finalize(); return; }
    stepIdx = idx;
    applyStep(steps[idx++]);
    const speed = parseInt(document.getElementById('speed').value);
    animTimer = setTimeout(next, speed);
  }
  next();
}

function runCYK() {
  clearAnim(); isStepMode = false;
  document.getElementById('next-btn').style.display = 'none';
  if (!prepare()) return;
  buildSteps();
  animateSteps();
}

function stepMode() {
  clearAnim(); isStepMode = true;
  if (!prepare()) return;
  buildSteps();
  stepIdx = 0;
  renderTable();
  showStatus('Step-by-step mode active — click "Next Step →" to advance.', 'info');
  document.getElementById('next-btn').style.display = '';
  document.getElementById('explain-panel').innerHTML =
    '<div class="empty-state"><span style="font-size:16px">⏭</span>Press <strong>Next Step →</strong> to begin filling the table.</div>';
}

function nextStep() {
  if (stepIdx >= steps.length) { finalize(); return; }
  applyStep(steps[stepIdx++]);
  if (stepIdx >= steps.length) setTimeout(finalize, 400);
}

function clearAnim() {
  if (animTimer) { clearTimeout(animTimer); animTimer = null; }
}

function finalize() {
  const accepted = dp[0][n - 1].has(startSym);
  const topCell = document.querySelector(`td[data-i="0"][data-j="${n - 1}"]`);
  if (topCell) {
    topCell.classList.remove('active-cell', 'new-var', 'done-cell');
    topCell.classList.add(accepted ? 'accept-cell' : 'reject-cell');
  }
  document.getElementById('progress-bar').style.width = '100%';
  showStatus(
    accepted
      ? `✓ ACCEPTED — "${w}" is in the language (${startSym} ∈ table[0][${n-1}])`
      : `✗ REJECTED — "${w}" is NOT in the language (${startSym} ∉ table[0][${n-1}])`,
    accepted ? 'accepted' : 'rejected'
  );
  if (isStepMode) document.getElementById('next-btn').style.display = 'none';
}

function showStatus(msg, type) {
  const el = document.getElementById('status-bar');
  el.textContent = msg;
  el.className = 'status-' + type;
  el.style.display = 'block';
}

function renderTable(activeI = -1, activeJ = -1, hasNew = false) {
  const wrap = document.getElementById('table-wrap');
  let html = '<table class="cyk"><thead><tr>';
  html += '<td class="row-label" style="border:none;background:transparent"></td>';
  for (let j = 0; j < n; j++)
    html += `<td class="col-header"><span class="col-char">${w[j]}</span><span class="col-idx">${j}</span></td>`;
  html += '</tr></thead><tbody>';

  for (let len = n; len >= 1; len--) {
    html += `<tr><td class="row-label">len ${len}</td>`;
    for (let j = 0; j < n; j++) {
      const i = j - (len - 1);
      if (i < 0 || i > j) { html += '<td class="empty-cell"></td>'; continue; }
      const vars = [...dp[i][j]];
      let cls = '';
      if (i === activeI && j === activeJ) cls = hasNew ? 'active-cell new-var' : 'active-cell';
      else if (vars.length > 0) cls = 'done-cell';
      html += `<td class="${cls}" data-i="${i}" data-j="${j}" onclick="clickCell(${i},${j})">`;
      html += `<span class="cell-pos">${i},${j}</span>`;
      const isComputed = cellDetails && cellDetails[i] && cellDetails[i][j] !== null;
      html += `<span class="cell-vars">${isComputed ? (vars.length > 0 ? vars.join('<br>') : '&empty;') : (vars.length > 0 ? vars.join('<br>') : '')}</span>`;
      html += '</td>';
    }
    html += '</tr>';
  }
  html += '</tbody></table>';
  wrap.innerHTML = html;
}

function clickCell(i, j) {
  const d = cellDetails[i][j];
  const panel = document.getElementById('explain-panel');
  if (!d) {
    panel.innerHTML = `
      <div class="explain-header">
        <span class="explain-cell-badge">(${i},${j})</span>
        <span style="color:var(--text3);font-size:12px">Not yet computed</span>
      </div>
      <div>Substring: <span class="tag tag-amber">"${w.slice(i,j+1)||w[i]}"</span> (positions ${i}–${j})</div>`;
    return;
  }
  updateExplain(i, j, d);
}

function updateExplain(i, j, d) {
  if (!d) return;
  const substr = d.substr || w.slice(i, j + 1);
  let html = `
    <div class="explain-header">
      <span class="explain-cell-badge">Cell (${i},${j})</span>
      <span>Substring: <span class="tag tag-blue">"${substr}"</span> (positions ${i}–${j})</span>
    </div>`;

  if (d.length === 1) {
    html += `<div style="margin-bottom:8px">Terminal lookup: character <span class="tag tag-amber">'${d.ch}'</span></div>`;
    if (d.vars.length > 0) {
      html += `<div>Variables generating <strong>'${d.ch}'</strong>: `;
      html += d.vars.map(v => `<span class="tag tag-green">${v}</span>`).join('  ') + '</div>';
    } else {
      html += `<div style="color:var(--text3)">No variables in the grammar generate '${d.ch}'.</div>`;
    }
  } else {
    if (d.splits.length === 0) {
      html += `<div style="color:var(--text3);padding:8px 0">No valid splits found — this cell is empty (∅).<br>None of the ${d.length - 1} possible split points produced matching grammar rules.</div>`;
    } else {
      html += `<div style="margin-bottom:8px;font-size:12px;color:var(--text2)">Testing all ${d.length - 1} split point(s) of <strong>"${substr}"</strong>:</div>`;
      const seen = new Set();
      for (const sp of d.splits) {
        const key = `${sp.k}:${sp.A}:${sp.B}:${sp.C}`;
        if (seen.has(key)) continue; seen.add(key);
        html += `
          <div class="split-item">
            <div>Split at <strong>k=${sp.k}</strong>: <span class="tag tag-amber">"${sp.left}"</span> · <span class="tag tag-amber">"${sp.right}"</span></div>
            <div style="margin-top:4px">Rule fired: <span class="tag tag-blue">${sp.A} → ${sp.B} ${sp.C}</span>
              <span style="color:var(--text3);font-size:11px;margin-left:6px">(${sp.B} ∈ [${i},${sp.k}] and ${sp.C} ∈ [${sp.k+1},${j}])</span>
            </div>
          </div>`;
      }
      if (d.vars.length > 0) {
        html += `<div style="margin-top:10px">Result: ` +
          d.vars.map(v => `<span class="tag tag-green">${v}</span>`).join('  ') + '</div>';
      }
    }
  }
  document.getElementById('explain-panel').innerHTML = html;
}

function resetAll() {
  clearAnim();
  G = {}; n = 0; w = ''; dp = []; steps = []; stepIdx = 0;
  isStepMode = false; cellDetails = []; totalSteps = 0;
  document.getElementById('stats-card').style.display = 'none';
  document.getElementById('status-bar').style.display = 'none';
  document.getElementById('next-btn').style.display = 'none';
  const cnfEl = document.getElementById('cnf-warn');
  cnfEl.style.display = 'none';
  cnfEl.style.background = '';
  cnfEl.style.borderColor = '';
  cnfEl.style.color = '';
  cnfEl.innerHTML = '';
  document.getElementById('progress-wrap').style.display = 'none';
  document.getElementById('progress-bar').style.width = '0%';
  document.getElementById('table-wrap').innerHTML =
    '<div class="empty-table"><div class="empty-table-icon">⊡</div><div>Run the algorithm to see the parsing table</div></div>';
  document.getElementById('explain-panel').innerHTML =
    '<div class="empty-state"><span style="font-size:16px">◎</span>Click any cell in the table to see how it was computed — or run the algorithm to begin.</div>';
}
