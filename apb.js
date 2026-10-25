/* PosEdge APB Lab — interactive engine
   Waveform generator, per-assertion checker, waveform renderer, FSM simulator,
   lab (watch / insert a bug / randomize / edit), bug hunt, checkpoint, quiz,
   roadmap and progress. No dependencies. */
(function () {
  'use strict';

  /* ================================================================
     1. Signal model and formatting
     ================================================================ */
  const SIG = {
    PCLK:    { kind: 'clk', grp: 'clk', w: 1 },
    PRESETn: { w: 1, grp: 'ctrl' },
    PWAKEUP: { w: 1, grp: 'ctrl' },
    PSEL:    { w: 1, grp: 'ctrl' },
    PSEL1:   { w: 1, grp: 'ctrl' },
    PSEL2:   { w: 1, grp: 'ctrl' },
    PENABLE: { w: 1, grp: 'ctrl' },
    PADDR:   { w: 32, grp: 'addr' },
    PWRITE:  { w: 1, grp: 'addr' },
    PPROT:   { w: 3, grp: 'addr' },
    PWDATA:  { w: 32, grp: 'wdata' },
    PSTRB:   { w: 4, grp: 'wdata' },
    PREADY:  { w: 1, grp: 'resp' },
    PRDATA:  { w: 32, grp: 'rdata' },
    PSLVERR: { w: 1, grp: 'resp' }
  };
  const PHLABEL = { IDLE: 'IDLE', SETUP: 'SETUP', ACCESS: 'ACCESS', WAIT: 'WAIT', RESET: 'RESET', BAD: 'ILLEGAL' };
  const MAX_WAIT = 16;

  const clone = o => JSON.parse(JSON.stringify(o));
  const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  const isX = v => v === 'x' || v === undefined || v === null;

  function hexs(v) {
    if (isX(v)) return 'X';
    if (v === 'z') return 'Z';
    return (v >>> 0).toString(16).toUpperCase();
  }
  function fmt(n, v) {
    if (isX(v)) return 'X';
    if (v === 'z') return 'Z';
    if (n === 'PSTRB') return v.toString(2).padStart(4, '0');
    if (n === 'PPROT') return v.toString(2).padStart(3, '0');
    if (SIG[n] && SIG[n].w > 1) return hexs(v);
    return String(v);
  }
  function fmtLong(n, v) {
    const s = fmt(n, v);
    if (s === 'X' || s === 'Z') return s;
    if (SIG[n] && SIG[n].w > 4) return '0x' + s.padStart(8, '0').replace(/(.{4})(.{4})/, '$1_$2');
    if (n === 'PSTRB' || n === 'PPROT') return "'b" + s;
    return s;
  }
  function protText(p) {
    if (isX(p)) return 'unknown protection';
    return [(p & 1) ? 'privileged' : 'normal', (p & 2) ? 'non-secure' : 'secure', (p & 4) ? 'instruction' : 'data'].join(', ');
  }
  function strbText(s) {
    if (isX(s)) return 'unknown byte lanes';
    if (s === 0) return 'no byte lanes, so nothing is written';
    const lanes = [0, 1, 2, 3].filter(b => (s >> b) & 1);
    if (lanes.length === 4) return 'all four byte lanes';
    return 'byte lane' + (lanes.length > 1 ? 's ' : ' ') + lanes.join(', ') + ' only (' +
      lanes.map(b => `PWDATA[${b * 8 + 7}:${b * 8}]`).join(', ') + ')';
  }

  /* ================================================================
     2. Waveform generator: transfer list -> cycle-accurate signals
     Cycle i lies between rising edges Ti and T(i+1); its values are
     sampled at T(i+1).
     ================================================================ */
  function generate(cfg) {
    const ver = cfg.ver;
    const txns = cfg.txns || [];
    const multi = txns.some(t => (t.slave || 1) !== 1);
    const sels = multi ? ['PSEL1', 'PSEL2'] : ['PSEL'];
    const C = [];
    let hold = { PADDR: 'x', PWRITE: 'x', PWDATA: 'x' };
    if (ver >= 4) { hold.PSTRB = 'x'; hold.PPROT = 'x'; }
    const blank = () => {
      const o = { PRESETn: 1, PENABLE: 0, PREADY: 0, PSLVERR: 0, PRDATA: 'x', PWAKEUP: 0 };
      sels.forEach(s => { o[s] = 0; });
      return Object.assign(o, hold);
    };
    for (let i = 0; i < (cfg.reset || 0); i++) { const o = blank(); o.PRESETn = 0; C.push(o); }
    const idle = cfg.idle === undefined ? 1 : cfg.idle;
    for (let i = 0; i < idle; i++) C.push(blank());
    const spans = [];
    txns.forEach((t, k) => {
      const sel = multi ? 'PSEL' + (t.slave || 1) : 'PSEL';
      const wr = t.write ? 1 : 0;
      hold = Object.assign({}, hold, { PADDR: t.addr >>> 0, PWRITE: wr, PWDATA: wr ? (t.data >>> 0) : hold.PWDATA });
      if (ver >= 4) {
        hold.PSTRB = wr ? (t.strb === undefined ? 15 : t.strb) : (t.strb || 0);
        hold.PPROT = t.prot || 0;
      }
      const start = C.length;
      let o = blank(); o[sel] = 1;
      if (t.readyEarly && ver >= 3) o.PREADY = 1;
      C.push(o);
      const waits = ver >= 3 ? Math.max(0, t.wait | 0) : 0;
      for (let j = 0; j <= waits; j++) {
        o = blank(); o[sel] = 1; o.PENABLE = 1;
        if (j === waits) {
          o.PREADY = 1;
          if (!wr) o.PRDATA = t.data >>> 0;
          if (ver >= 3 && t.err) o.PSLVERR = 1;
        }
        C.push(o);
      }
      spans.push([start, C.length - 1]);
      const gap = t.gap === undefined ? (k === txns.length - 1 ? 2 : 0) : t.gap;
      for (let g = 0; g < gap; g++) C.push(blank());
    });
    if (!txns.length) for (let i = 0; i < 4; i++) C.push(blank());
    if (ver >= 5 && spans.length) {
      const lead = cfg.wake === undefined ? 1 : cfg.wake;
      const a = Math.max(0, spans[0][0] - lead), b = spans[spans.length - 1][1];
      for (let i = a; i <= b; i++) C[i].PWAKEUP = 1;
    }
    const lanes = ['PCLK'];
    if (cfg.reset) lanes.push('PRESETn');
    if (ver >= 5) lanes.push('PWAKEUP');
    lanes.push(...sels, 'PENABLE', 'PADDR', 'PWRITE');
    if (ver >= 4) lanes.push('PPROT');
    lanes.push('PWDATA');
    if (ver >= 4) lanes.push('PSTRB');
    if (ver >= 3) lanes.push('PREADY');
    lanes.push('PRDATA');
    if (ver >= 3) lanes.push('PSLVERR');
    return { ver, lanes, sels, cycles: C };
  }

  /* ================================================================
     3. Phases and the assertion model
     Each assertion mirrors one property of the SVA checker (chapter 09).
     ev() records every attempt (antecedent true) and every failure,
     with the cycle the attempt started in, so the page can draw them.
     ================================================================ */
  const anySel = (w, c) => w.sels.some(s => c[s] === 1);
  const selVec = (w, c) => w.sels.map(s => (c[s] === 1 ? 1 : 0)).join('');
  const rdy = (w, c) => (w.ver < 3 ? 1 : c.PREADY);

  function phaseOf(w, i) {
    const c = w.cycles[i];
    if (c.PRESETn === 0) return 'RESET';
    if (!anySel(w, c)) return c.PENABLE === 1 ? 'BAD' : 'IDLE';
    if (c.PENABLE !== 1) return 'SETUP';
    return rdy(w, c) === 1 ? 'ACCESS' : 'WAIT';
  }

  function flags(w) {
    return w.cycles.map(c => {
      const live = c.PRESETn !== 0, sel = anySel(w, c), en = c.PENABLE === 1, r = rdy(w, c) === 1;
      return { live, sel, en, setup: live && sel && !en, access: live && sel && en, wait: live && sel && en && !r, done: live && sel && en && r, sv: selVec(w, c) };
    });
  }
  const ctrlNames = w => ['PADDR', 'PWRITE'].concat(w.ver >= 4 ? ['PPROT'] : []);
  const wdNames = w => ['PWDATA'].concat(w.ver >= 4 ? ['PSTRB'] : []);
  const movedMsg = (w, names, j, i) => {
    const C = w.cycles;
    const m = names.filter(n => C[j][n] !== C[i][n]);
    return m.map(n => `${n} ${fmtLong(n, C[i][n])} → ${fmtLong(n, C[j][n])}`).join(', ') + ' changed while the transfer was still in progress.';
  };
  const xList = (w, i, names) => names.filter(n => isX(w.cycles[i][n]));

  // same-cycle implication (|->) and "always" checks
  function same(ante, cons, msg, noDisable) {
    return (w, f, r) => {
      for (let i = 0; i < f.length; i++) {
        if (!noDisable && !f[i].live) continue;
        if (!ante(w, f, i)) continue;
        r.att.push(i);
        if (!cons(w, f, i)) r.fails.push({ i, from: i, msg: typeof msg === 'function' ? msg(w, f, i) : msg });
      }
    };
  }
  // next-cycle implication (|=>)
  function next(ante, cons, msg) {
    return (w, f, r) => {
      for (let i = 0; i + 1 < f.length; i++) {
        if (!f[i].live || !f[i + 1].live) continue;
        if (!ante(w, f, i)) continue;
        r.att.push(i);
        if (!cons(w, f, i + 1, i)) r.fails.push({ i: i + 1, from: i, msg: typeof msg === 'function' ? msg(w, f, i + 1, i) : msg });
      }
    };
  }

  const ASSERTS = [
    {
      name: 'a_reset_idle', tag: 'Reset', sev: 'error', ver: 2, op: '|->', ante: '!PRESETn', cons: '!PSEL && !PENABLE',
      meaning: 'While reset is asserted, PSEL and PENABLE are low.',
      sva: "a_reset_idle: assert property (@(posedge PCLK) disable iff (1'b0)\n  !PRESETn |-> !(|PSELx) && !PENABLE);",
      ev: same((w, f, i) => w.cycles[i].PRESETn === 0, (w, f, i) => !f[i].sel && !f[i].en, 'PSEL or PENABLE is high during reset.', true)
    },
    {
      name: 'a_no_x_sel', tag: 'X-check', sev: 'error', ver: 2, op: 'always', ante: 'every clock', cons: '!$isunknown({PSELx, PENABLE})',
      meaning: 'PSEL and PENABLE are never X outside reset.',
      sva: 'a_no_x_sel: assert property (!$isunknown({PSELx, PENABLE}));',
      ev: same(() => true, (w, f, i) => !w.sels.concat(['PENABLE']).some(s => isX(w.cycles[i][s])), (w, f, i) => xList(w, i, w.sels.concat(['PENABLE'])).join(', ') + ' is X.')
    },
    {
      name: 'a_psel_onehot', tag: 'Decoder', sev: 'error', ver: 2, op: 'always', ante: 'every clock', cons: '$onehot0(PSELx)',
      meaning: 'At most one completer is selected at a time.',
      sva: 'a_psel_onehot: assert property ($onehot0(PSELx));',
      ev: same(() => true, (w, f, i) => w.sels.filter(s => w.cycles[i][s] === 1).length <= 1, (w, f, i) => w.sels.filter(s => w.cycles[i][s] === 1).join(' and ') + ' are high together, so two completers drive PREADY and PRDATA.')
    },
    {
      name: 'a_en_needs_sel', tag: 'Rule 3', sev: 'error', ver: 2, op: '|->', ante: 'PENABLE', cons: '|PSELx',
      meaning: 'PENABLE is never high without a PSEL.',
      sva: 'a_en_needs_sel: assert property (PENABLE |-> |PSELx);',
      ev: same((w, f, i) => f[i].en, (w, f, i) => f[i].sel, 'PENABLE is high but no PSEL is.')
    },
    {
      name: 'a_setup_to_access', tag: 'Rule 1', sev: 'error', ver: 2, op: '|=>', ante: 'SETUP (PSEL && !PENABLE)', cons: 'ACCESS to the same PSELx',
      meaning: 'SETUP lasts exactly one cycle, then ACCESS to the same completer.',
      sva: 'a_setup_to_access: assert property (setup_ph |=> access_ph && $stable(PSELx));',
      ev: next((w, f, i) => f[i].setup, (w, f, j, i) => f[j].access && f[j].sv === f[i].sv,
        (w, f, j) => f[j].setup ? 'PENABLE is still low, so SETUP lasted two cycles.' : f[j].sel ? 'PSEL changed between SETUP and ACCESS.' : 'PSEL dropped right after SETUP.')
    },
    {
      name: 'a_rose_en_after_setup', tag: 'Rule 1', sev: 'error', ver: 2, op: '|->', ante: '$rose(PENABLE)', cons: '$past(setup_ph)',
      meaning: 'PENABLE only rises after a SETUP cycle.',
      sva: 'a_rose_en_after_setup: assert property ($rose(PENABLE) |-> $past(setup_ph));',
      ev: (w, f, r) => {
        for (let i = 1; i < f.length; i++) {
          if (!f[i].live || w.cycles[i - 1].PENABLE === 1 || w.cycles[i].PENABLE !== 1) continue;
          r.att.push(i);
          if (!f[i - 1].setup) r.fails.push({ i, from: i, msg: 'PENABLE rose without a SETUP cycle before it.' });
        }
      }
    },
    {
      name: 'a_wait_hold', tag: 'Rule 2', sev: 'error', ver: 3, op: '|=>', ante: 'wait state (ACCESS && !PREADY)', cons: 'still ACCESS, same PSELx',
      meaning: 'While PREADY is low, PSEL and PENABLE stay high.',
      sva: 'a_wait_hold: assert property (wait_ph |=> access_ph && $stable(PSELx));',
      ev: next((w, f, i) => f[i].wait, (w, f, j, i) => f[j].access && f[j].sv === f[i].sv,
        (w, f, j) => f[j].sel ? 'The selected completer changed during a wait state.' : 'PSEL or PENABLE dropped before PREADY was high. APB has no abort.')
    },
    {
      name: 'a_stable_ctrl', tag: 'Rule 2', sev: 'error', ver: 2, op: '|=>', ante: 'SETUP or a wait state', cons: '$stable({PADDR, PWRITE, PPROT})',
      meaning: 'Address and control hold from SETUP until completion.',
      sva: 'a_stable_ctrl: assert property ((setup_ph || wait_ph) |=> $stable({PADDR, PWRITE, PPROT}));',
      ev: next((w, f, i) => f[i].setup || f[i].wait, (w, f, j, i) => ctrlNames(w).every(n => w.cycles[j][n] === w.cycles[i][n]),
        (w, f, j, i) => movedMsg(w, ctrlNames(w), j, i))
    },
    {
      name: 'a_stable_wdata', tag: 'Rule 2', sev: 'error', ver: 2, op: '|=>', ante: 'a write in SETUP or a wait state', cons: '$stable({PWDATA, PSTRB})',
      meaning: 'Write data and strobes hold until the write completes.',
      sva: 'a_stable_wdata: assert property ((setup_ph || wait_ph) && PWRITE |=> $stable({PWDATA, PSTRB}));',
      ev: next((w, f, i) => (f[i].setup || f[i].wait) && w.cycles[i].PWRITE === 1, (w, f, j, i) => wdNames(w).every(n => w.cycles[j][n] === w.cycles[i][n]),
        (w, f, j, i) => movedMsg(w, wdNames(w), j, i))
    },
    {
      name: 'a_en_drop', tag: 'Rule 4', sev: 'error', ver: 2, op: '|=>', ante: 'completion (PSEL && PENABLE && PREADY)', cons: '!PENABLE',
      meaning: 'PENABLE goes low in the cycle after every completion.',
      sva: 'a_en_drop: assert property (done_ph |=> !PENABLE);',
      ev: next((w, f, i) => f[i].done, (w, f, j) => !f[j].en, 'PENABLE is still high after the transfer completed, so the next transfer has no SETUP.')
    },
    {
      name: 'a_strb_read', tag: 'APB4', sev: 'error', ver: 4, op: '|->', ante: 'a read is selected (PSEL && !PWRITE)', cons: "PSTRB == '0",
      meaning: 'PSTRB is all zeros during reads.',
      sva: "a_strb_read: assert property (|PSELx && !PWRITE |-> PSTRB == '0);",
      ev: same((w, f, i) => f[i].sel && w.cycles[i].PWRITE === 0, (w, f, i) => w.cycles[i].PSTRB === 0 || isX(w.cycles[i].PSTRB),
        (w, f, i) => `PSTRB is ${fmt('PSTRB', w.cycles[i].PSTRB)} during a read.`)
    },
    {
      name: 'a_no_x_ctrl', tag: 'X-check', sev: 'error', ver: 2, op: '|->', ante: 'PSEL', cons: '!$isunknown({PADDR, PWRITE, PPROT})',
      meaning: 'Address and control are never X while selected.',
      sva: 'a_no_x_ctrl: assert property (|PSELx |-> !$isunknown({PADDR, PWRITE, PPROT}));',
      ev: same((w, f, i) => f[i].sel, (w, f, i) => !xList(w, i, ctrlNames(w)).length, (w, f, i) => xList(w, i, ctrlNames(w)).join(', ') + ' is X while PSEL is high.')
    },
    {
      name: 'a_no_x_wdata', tag: 'X-check', sev: 'error', ver: 2, op: '|->', ante: 'PSEL && PWRITE', cons: '!$isunknown({PWDATA, PSTRB})',
      meaning: 'Write data and strobes are never X during a write.',
      sva: 'a_no_x_wdata: assert property (|PSELx && PWRITE |-> !$isunknown({PWDATA, PSTRB}));',
      ev: same((w, f, i) => f[i].sel && w.cycles[i].PWRITE === 1, (w, f, i) => !xList(w, i, wdNames(w)).length, (w, f, i) => xList(w, i, wdNames(w)).join(', ') + ' is X during a write.')
    },
    {
      name: 'a_no_x_ready', tag: 'X-check', sev: 'error', ver: 3, op: '|->', ante: 'ACCESS', cons: '!$isunknown(PREADY)',
      meaning: 'PREADY is never X in the ACCESS phase.',
      sva: 'a_no_x_ready: assert property (access_ph |-> !$isunknown(PREADY));',
      ev: same((w, f, i) => f[i].access, (w, f, i) => !isX(w.cycles[i].PREADY), 'PREADY is X in ACCESS, so nobody knows whether the transfer is finished.')
    },
    {
      name: 'a_no_x_err', tag: 'X-check', sev: 'error', ver: 3, op: '|->', ante: 'completion', cons: '!$isunknown(PSLVERR)',
      meaning: 'PSLVERR is never X when a transfer completes.',
      sva: 'a_no_x_err: assert property (done_ph |-> !$isunknown(PSLVERR));',
      ev: same((w, f, i) => f[i].done, (w, f, i) => !isX(w.cycles[i].PSLVERR), 'PSLVERR is X at completion.')
    },
    {
      name: 'a_no_x_rdata', tag: 'Rule 5', sev: 'error', ver: 2, op: '|->', ante: 'a read completes without error', cons: '!$isunknown(PRDATA)',
      meaning: 'PRDATA is valid at the triple-high edge of a read.',
      sva: 'a_no_x_rdata: assert property (done_ph && !PWRITE && !PSLVERR |-> !$isunknown(PRDATA));',
      ev: same((w, f, i) => f[i].done && w.cycles[i].PWRITE === 0 && w.cycles[i].PSLVERR !== 1, (w, f, i) => !isX(w.cycles[i].PRDATA), 'PRDATA is X in the one cycle where the requester samples it.')
    },
    {
      name: 'a_err_only_on_done', tag: 'Rule 5', sev: 'warn', ver: 3, op: '|->', ante: 'PSLVERR', cons: 'completion',
      meaning: 'PSLVERR is driven low outside the completing cycle (recommended).',
      sva: 'a_err_only_on_done: assert property (PSLVERR |-> done_ph)\n  else $warning("PSLVERR high outside the completing cycle");',
      ev: same((w, f, i) => w.cycles[i].PSLVERR === 1, (w, f, i) => f[i].done, 'PSLVERR is high outside the completing cycle. Legal, but the requester must ignore it there.')
    },
    {
      name: 'a_max_wait', tag: 'Policy', sev: 'warn', ver: 3, op: '##', ante: 'SETUP', cons: `completion within ${MAX_WAIT + 1} clocks`,
      meaning: `A transfer completes within ${MAX_WAIT} wait states (testbench policy).`,
      sva: `a_max_wait: assert property (setup_ph |-> ##[1:${MAX_WAIT + 1}] done_ph)\n  else $warning("Transfer exceeded ${MAX_WAIT} wait states");`,
      ev: (w, f, r) => {
        for (let i = 0; i < f.length; i++) {
          if (!f[i].setup) continue;
          r.att.push(i);
          const end = i + MAX_WAIT + 1;
          let ok = false;
          for (let j = i + 1; j <= Math.min(end, f.length - 1); j++) { if (!f[j].live) { ok = true; break; } if (f[j].done) { ok = true; break; } }
          if (!ok && end <= f.length - 1) r.fails.push({ i: end, from: i, msg: `No completion within ${MAX_WAIT} wait states. APB allows this, but a stalled completer hangs the bus without a watchdog.` });
        }
      }
    },
    {
      name: 'a_wake_during_xfer', tag: 'APB5', sev: 'warn', ver: 5, op: '|->', ante: 'PSEL', cons: 'PWAKEUP',
      meaning: 'PWAKEUP is high whenever a transfer is in progress (recommended).',
      sva: 'a_wake_during_xfer: assert property (|PSELx |-> PWAKEUP)\n  else $warning("PWAKEUP low during a transfer");',
      ev: same((w, f, i) => f[i].sel, (w, f, i) => w.cycles[i].PWAKEUP === 1, 'PWAKEUP is low during a transfer.')
    }
  ];
  const PLAIN = {
    a_reset_idle: 'During reset, nothing is selected and nothing is enabled.',
    a_no_x_sel: 'PSEL and PENABLE always have a real 0 or 1.',
    a_psel_onehot: 'Never select two peripherals at the same time.',
    a_en_needs_sel: 'No PENABLE without a PSEL.',
    a_setup_to_access: 'After one SETUP cycle comes ACCESS, to the same peripheral.',
    a_rose_en_after_setup: 'PENABLE may only switch on right after a SETUP cycle.',
    a_wait_hold: 'While the peripheral is not ready, keep it selected and enabled.',
    a_stable_ctrl: 'Once the address is on the bus, it must not change until the transfer ends.',
    a_stable_wdata: 'Once the write data is on the bus, it must not change until the write ends.',
    a_en_drop: 'After a transfer ends, PENABLE switches off for at least one cycle.',
    a_strb_read: 'Reads never carry byte strobes.',
    a_no_x_ctrl: 'While selected, the address, direction and protection have real values.',
    a_no_x_wdata: 'During a write, the data and strobes have real values.',
    a_no_x_ready: 'In ACCESS, PREADY is a real 0 or 1.',
    a_no_x_err: 'When a transfer ends, PSLVERR is a real 0 or 1.',
    a_no_x_rdata: 'When a read ends without an error, the read data is real.',
    a_err_only_on_done: 'PSLVERR should only be high in the cycle the transfer ends.',
    a_max_wait: `No transfer waits more than ${MAX_WAIT} cycles (our testbench limit).`,
    a_wake_during_xfer: 'PWAKEUP stays high for the whole transfer.'
  };
  ASSERTS.forEach(a => { a.plain = PLAIN[a.name]; });
  const AMAP = Object.fromEntries(ASSERTS.map(a => [a.name, a]));

  function evalAll(w) {
    const f = flags(w);
    return ASSERTS.filter(a => w.ver >= a.ver).map(a => { const r = { att: [], fails: [] }; a.ev(w, f, r); return { a, att: r.att, fails: r.fails }; });
  }
  function check(w) {
    const out = [];
    evalAll(w).forEach(R => R.fails.forEach(x => out.push({ i: x.i, from: x.from, rule: R.a.name, sev: R.a.sev, msg: x.msg })));
    return out.sort((p, q) => p.i - q.i);
  }

  /* ================================================================
     4. Plain-English explanation of a cycle
     ================================================================ */
  function explain(w, i) {
    const C = w.cycles, c = C[i], ph = phaseOf(w, i);
    const T = `T${i + 1}`;
    const wr = c.PWRITE === 1;
    const sel = w.sels.find(s => c[s] === 1) || 'PSEL';
    const code = s => `<code>${s}</code>`;
    switch (ph) {
      case 'RESET':
        return `${code('PRESETn')} is low, so the bus is in reset. ${code('PSEL')} and ${code('PENABLE')} must be low and nothing is transferred.`;
      case 'IDLE': {
        let t = 'IDLE: no completer is selected, so nothing happens.';
        if (i > 0 && phaseOf(w, i - 1) === 'ACCESS') t += ' The previous transfer has just finished and nothing else is pending.';
        if (i > 0 && phaseOf(w, i - 1) === 'RESET') t += ' Reset has just been released.';
        if (w.ver >= 5 && c.PWAKEUP === 1) t += ` ${code('PWAKEUP')} is already high, warning the completer that a transfer is coming so it can ungate its clock.`;
        else t += ` ${code('PADDR')} and ${code('PWRITE')} may hold their last value, which saves switching power.`;
        return t;
      }
      case 'SETUP': {
        let t = `SETUP: ${code(sel)} is high and ${code('PENABLE')} is low. The requester presents a <b>${wr ? 'write' : 'read'}</b> to ${code('PADDR')}=${fmtLong('PADDR', c.PADDR)}`;
        if (wr) t += ` with ${code('PWDATA')}=${fmtLong('PWDATA', c.PWDATA)}`;
        if (w.ver >= 4) t += `, ${code('PPROT')}=${fmt('PPROT', c.PPROT)} (${protText(c.PPROT)})` + (wr ? `, ${code('PSTRB')}=${fmt('PSTRB', c.PSTRB)}` : '');
        t += `. SETUP always lasts exactly one cycle, so after ${T} the bus is in ACCESS.`;
        if (w.ver >= 3 && c.PREADY === 1) t += ` ${code('PREADY')} is already high, but it is ignored here: PREADY is only sampled in ACCESS.`;
        return t;
      }
      case 'WAIT': {
        let k = 1;
        for (let j = i - 1; j >= 0 && phaseOf(w, j) === 'WAIT'; j--) k++;
        let t = `ACCESS with ${code('PREADY')} low: <b>wait state ${k}</b>. The completer is not ready, so nothing completes at ${T}. The requester keeps ${code(sel)}, ${code('PENABLE')}, ${code('PADDR')}, ${code('PWRITE')}`;
        if (wr) t += `, ${code('PWDATA')}`;
        if (w.ver >= 4) t += `, ${code('PPROT')} and ${code('PSTRB')}`;
        return t + ' frozen.';
      }
      case 'ACCESS': {
        let t = `<b>Triple-high edge at ${T}</b>: ${code(sel)}, ${code('PENABLE')}` + (w.ver >= 3 ? ` and ${code('PREADY')} are all high, so the transfer completes.` : ' are high (APB2 has no PREADY, so ACCESS is always one cycle).');
        if (wr) {
          t += ` The completer captures ${code('PWDATA')}=${fmtLong('PWDATA', c.PWDATA)} at ${fmtLong('PADDR', c.PADDR)}`;
          t += w.ver >= 4 ? `, using ${strbText(c.PSTRB)}.` : '.';
        } else t += ` The requester samples ${code('PRDATA')}=${fmtLong('PRDATA', c.PRDATA)}.`;
        if (w.ver >= 3 && c.PSLVERR === 1) t += ` <b>${code('PSLVERR')} is high, so the transfer failed.</b> ` + (wr ? 'The register may or may not have been written.' : 'The read data is not guaranteed to be valid.');
        const n = i + 1 < C.length ? phaseOf(w, i + 1) : null;
        if (n === 'SETUP') t += ' Another transfer follows immediately, so the next cycle is SETUP: PSEL stays high and PENABLE drops.';
        else if (n === 'IDLE') t += ' Nothing is pending, so the bus returns to IDLE.';
        return t;
      }
      default:
        return `${code('PENABLE')} is high with no ${code('PSEL')}. This is not a legal APB state.`;
    }
  }

  /* ================================================================
     5. Data: scenarios, puzzles, bugs, quizzes, chapters
     ================================================================ */
  const SGRP = ['APB2 · the basics', 'APB3 · waits and errors', 'Back-to-back', 'APB4 · strobes and protection', 'APB5 · wake-up', 'Corner cases'];
  const PRESETS = [
    { id: 'apb2-write', grp: SGRP[0], short: 'Simple write', learn: 'The two-cycle transfer', focus: 'a_setup_to_access', name: 'APB2 · write, no wait states', tip: 'Two cycles and done: SETUP, then the write lands at the triple-high edge. APB2 has no way to wait.', cfg: { ver: 2, txns: [{ write: 1, addr: 0x10, data: 0xA5A50001 }] } },
    { id: 'apb2-read', grp: SGRP[0], short: 'Simple read', learn: 'When read data counts', focus: 'a_no_x_rdata', name: 'APB2 · read', tip: 'PRDATA only matters at the completing edge. Before that it is X, and nobody cares.', cfg: { ver: 2, txns: [{ write: 0, addr: 0x14, data: 0x0000BEEF }] } },
    { id: 'apb2-b2b', grp: SGRP[0], short: 'Write, then read', learn: 'Two transfers in a row', focus: 'a_en_drop', name: 'APB2 · write then read, back-to-back', tip: 'Between the two transfers PSEL stays high. Only PENABLE drops, for the second SETUP.', cfg: { ver: 2, txns: [{ write: 1, addr: 0x18, data: 0x00001234, gap: 0 }, { write: 0, addr: 0x18, data: 0x00001234 }] } },
    { id: 'apb3-wait-w', grp: SGRP[1], short: 'Write with waits', learn: 'Everything freezes until PREADY', focus: 'a_stable_ctrl', name: 'APB3 · write with 2 wait states', tip: 'PREADY is low for two cycles. Watch PADDR and PWDATA: they do not move until PREADY rises.', cfg: { ver: 3, txns: [{ write: 1, addr: 0x20, data: 0xDEADBEEF, wait: 2 }] } },
    { id: 'apb3-wait-r', grp: SGRP[1], short: 'Read with a wait', learn: 'Read data arrives late', focus: 'a_wait_hold', name: 'APB3 · read with 1 wait state', tip: 'One wait state. The read data appears only in the cycle where PREADY is high.', cfg: { ver: 3, txns: [{ write: 0, addr: 0x24, data: 0x00C0FFEE, wait: 1 }] } },
    { id: 'apb3-err', grp: SGRP[1], short: 'Error response', learn: 'When PSLVERR counts', focus: 'a_err_only_on_done', name: 'APB3 · error response (PSLVERR)', tip: 'PSLVERR is high only in the completing cycle of each transfer. That is the only place it counts.', cfg: { ver: 3, txns: [{ write: 1, addr: 0xFF0, data: 0x1, wait: 1, err: 1, gap: 1 }, { write: 0, addr: 0xFF4, data: 0x0, err: 1 }] } },
    { id: 'b2b', grp: SGRP[2], short: 'Same peripheral', learn: 'No idle between transfers', focus: 'a_en_drop', name: 'Back-to-back · write then read, same peripheral', tip: 'No IDLE between transfers. The second one starts with SETUP right after the first completes.', cfg: { ver: 3, txns: [{ write: 1, addr: 0x30, data: 0x11223344, gap: 0 }, { write: 0, addr: 0x30, data: 0x11223344, wait: 1 }] } },
    { id: 'two-slaves', grp: SGRP[2], short: 'Two peripherals', learn: 'PSEL1 hands over to PSEL2', focus: 'a_psel_onehot', name: 'Back-to-back · two peripherals (PSEL1, PSEL2)', tip: 'PSEL1 falls in the same cycle PSEL2 rises. Address and data wires are shared; only the select changes.', cfg: { ver: 3, txns: [{ slave: 1, write: 1, addr: 0x1000, data: 0xAAAA5555, gap: 0 }, { slave: 2, write: 0, addr: 0x2000, data: 0x5555AAAA, wait: 1 }] } },
    { id: 'apb4-strb', grp: SGRP[3], short: 'Byte strobes', learn: 'Writing only some bytes', focus: 'a_stable_wdata', name: 'APB4 · partial write with PSTRB, then read back', tip: 'PSTRB = 0011 writes the low two bytes only. The read back returns the merged word, and PSTRB is 0000 on the read.', cfg: { ver: 4, txns: [{ write: 1, addr: 0x40, data: 0x0000ABCD, strb: 3, prot: 2, wait: 1, gap: 1 }, { write: 0, addr: 0x40, data: 0x1234ABCD, prot: 2 }] } },
    { id: 'apb4-prot', grp: SGRP[3], short: 'Protection', learn: 'Secure and privileged access', focus: 'a_strb_read', name: 'APB4 · PPROT secure / non-secure / privileged', tip: 'Three reads with different PPROT. The last one is privileged and non-secure, and this completer rejects it with PSLVERR.', cfg: { ver: 4, txns: [{ write: 0, addr: 0x80, data: 0x1, prot: 0, gap: 0 }, { write: 0, addr: 0x84, data: 0x2, prot: 1, gap: 0 }, { write: 0, addr: 0x88, data: 0x3, prot: 3, err: 1 }] } },
    { id: 'apb5-wake', grp: SGRP[4], short: 'Wake-up', learn: 'PWAKEUP rises before PSEL', focus: 'a_wake_during_xfer', name: 'APB5 · PWAKEUP ahead of PSEL', tip: 'PWAKEUP rises two cycles before PSEL, so a clock-gated completer can wake up in time.', cfg: { ver: 5, wake: 2, idle: 3, txns: [{ write: 1, addr: 0x50, data: 0x0F0F0F0F, wait: 1, gap: 0 }, { write: 0, addr: 0x54, data: 0x600DCAFE }] } },
    { id: 'reset', grp: SGRP[5], short: 'After reset', learn: 'The very first transfer', focus: 'a_reset_idle', name: 'Reset, then the first transfer', tip: 'PSEL and PENABLE stay low while PRESETn is low. The first transfer can start right after release.', cfg: { ver: 3, reset: 3, idle: 1, txns: [{ write: 1, addr: 0x0, data: 0x1 }] } },
    { id: 'ready-early', grp: SGRP[5], short: 'Early PREADY', learn: 'PREADY ignored in SETUP', focus: 'a_rose_en_after_setup', name: 'Corner case · PREADY high during SETUP', tip: 'PREADY is already high in SETUP, but it is ignored there. The transfer still takes two cycles.', cfg: { ver: 3, txns: [{ write: 0, addr: 0x60, data: 0x7, readyEarly: 1 }] } },
    { id: 'timeout', grp: SGRP[5], short: 'Long stall', learn: 'A completer that will not answer', focus: 'a_max_wait', name: 'Corner case · completer stalls for 18 cycles', tip: 'The completer holds PREADY low for 18 cycles. APB allows it; the a_max_wait policy check warns.', cfg: { ver: 3, txns: [{ write: 0, addr: 0x70, data: 0x99, wait: 18 }] } }
  ];
  const presetById = id => PRESETS.find(p => p.id === id);

  const phasesOf = w => w.cycles.map((_, i) => phaseOf(w, i));
  const nth = (w, ph, k) => phasesOf(w).reduce((a, p, i) => (p === ph ? a.concat(i) : a), [])[k];
  const doneFrom = (w, i) => { const ph = phasesOf(w); for (let j = i; j < ph.length; j++) if (ph[j] === 'ACCESS') return j; return ph.length - 1; };

  // shared mutations, used by both the bug hunt and the bug-insertion lab
  const MUT = {
    addrWander(w) { const i = nth(w, 'WAIT', 1), e = doneFrom(w, i); for (let j = i; j <= e; j++) w.cycles[j].PADDR = 0x44; },
    noSetup(w) { w.cycles[nth(w, 'SETUP', 0)].PENABLE = 1; },
    giveUp(w) { const i = nth(w, 'WAIT', 1), e = doneFrom(w, i); for (let j = i; j <= e; j++) Object.assign(w.cycles[j], { PSEL: 0, PENABLE: 0, PREADY: 0, PRDATA: 'x' }); },
    enStuck(w) { w.cycles[nth(w, 'SETUP', 1)].PENABLE = 1; },
    strbRead(w) { w.cycles.forEach(c => { if (c.PSEL === 1) c.PSTRB = 15; }); },
    wdataChange(w) { const i = nth(w, 'WAIT', 1), e = doneFrom(w, i); for (let j = i; j <= e; j++) w.cycles[j].PWDATA = 0x0BADF00D; },
    rdataX(w) { w.cycles[nth(w, 'ACCESS', 0)].PRDATA = 'x'; },
    twoSel(w) { w.cycles[nth(w, 'ACCESS', 0)].PSEL2 = 1; },
    overlapSel(w) { const s2 = w.cycles.findIndex(c => c.PSEL2 === 1); w.cycles.forEach((c, i) => { if (i < s2 && c.PSEL1 === 1) c.PSEL2 = 1; }); },
    longSetup(w) { const s = nth(w, 'SETUP', 0); w.cycles.splice(s, 0, clone(w.cycles[s])); },
    enAlone(w) { const a = nth(w, 'ACCESS', 0); w.cycles[a + 1].PENABLE = 1; },
    errEarly(w) { w.cycles.forEach(c => { if (c.PSEL === 1) c.PSLVERR = 1; }); },
    readyX(w) { w.cycles.forEach((c, i) => { if (phaseOf(w, i) === 'WAIT') c.PREADY = 'x'; }); },
    protX(w) { w.cycles.forEach(c => { c.PPROT = 'x'; }); }
  };

  const PUZZLES = [
    { title: 'The address wanders', cfg: { ver: 3, txns: [{ write: 1, addr: 0x40, data: 0x12345678, wait: 2 }] }, mutate: MUT.addrWander,
      hint: 'Compare PADDR in every cycle from SETUP to the completing cycle.',
      explain: 'PADDR moves from 0x40 to 0x44 in the second wait state. Address and control must stay stable from SETUP until the cycle where PREADY is high. Caught by <code>a_stable_ctrl</code>.' },
    { title: 'Straight into ACCESS', cfg: { ver: 3, txns: [{ write: 0, addr: 0x08, data: 0xCAFE0001, wait: 0 }] }, mutate: MUT.noSetup,
      hint: 'Look at the first cycle where PSEL is high. What should PENABLE be there?',
      explain: 'PSEL and PENABLE rise together, so the transfer has no SETUP phase. PENABLE may only rise one cycle after PSEL. Caught by <code>a_rose_en_after_setup</code>.' },
    { title: 'The requester gives up', cfg: { ver: 3, txns: [{ write: 0, addr: 0x2C, data: 0x0000F00D, wait: 3 }] }, mutate: MUT.giveUp,
      hint: 'PREADY never goes high. What is the requester allowed to do while PREADY is low?',
      explain: 'PSEL and PENABLE drop during a wait state, abandoning the transfer. APB has no abort: the requester must hold until PREADY is high. Caught by <code>a_wait_hold</code>.' },
    { title: 'Back-to-back without a break', cfg: { ver: 3, txns: [{ write: 1, addr: 0x10, data: 0x000000AA, gap: 0 }, { write: 1, addr: 0x14, data: 0x000000BB, wait: 1 }] }, mutate: MUT.enStuck,
      hint: 'PSEL may stay high between back-to-back transfers. Does PENABLE behave correctly?',
      explain: 'After the first transfer completes, PENABLE stays high, so the second transfer never gets its SETUP cycle. PENABLE must drop for one cycle between transfers. Caught by <code>a_en_drop</code>.' },
    { title: 'Strobes on a read', cfg: { ver: 4, txns: [{ write: 0, addr: 0x08, data: 0x11112222, wait: 1, prot: 0 }] }, mutate: MUT.strbRead,
      hint: 'This is APB4. Check the signals that APB4 added.',
      explain: 'PSTRB is 1111 during a read. The APB4 specification requires PSTRB to be driven low for reads. Caught by <code>a_strb_read</code>.' },
    { title: 'Write data that will not sit still', cfg: { ver: 3, txns: [{ write: 1, addr: 0x34, data: 0x00C0FFEE, wait: 2 }] }, mutate: MUT.wdataChange,
      hint: 'Which value will the completer capture at the completing edge, and is it the value from SETUP?',
      explain: 'PWDATA changes in the second wait state, so the completer captures 0x0BADF00D instead of 0x00C0FFEE. PWDATA must hold for the whole write. Caught by <code>a_stable_wdata</code>.' },
    { title: 'Read data that never arrives', cfg: { ver: 3, txns: [{ write: 0, addr: 0x3C, data: 0x89ABCDEF, wait: 1 }] }, mutate: MUT.rdataX,
      hint: 'Check PRDATA at the one edge where the requester samples it.',
      explain: 'PRDATA is X in the completing cycle of the read, which is the only cycle where it is sampled. Caught by <code>a_no_x_rdata</code>.' },
    { title: 'Two completers at once', cfg: { ver: 3, txns: [{ slave: 1, write: 1, addr: 0x1000, data: 0x0000CAFE, wait: 1, gap: 0 }, { slave: 2, write: 0, addr: 0x2000, data: 0x0000BEEF }] }, mutate: MUT.twoSel,
      hint: 'Look at the select lines together, cycle by cycle.',
      explain: 'PSEL1 and PSEL2 are both high in one cycle. The decoder must select at most one completer, otherwise two completers drive PREADY and PRDATA. Caught by <code>a_psel_onehot</code>, and PSEL changing mid-transfer also breaks <code>a_wait_hold</code>.' },
    { title: 'A SETUP that lingers', cfg: { ver: 3, txns: [{ write: 1, addr: 0x20, data: 0x00000042, wait: 0 }] }, mutate: MUT.longSetup,
      hint: 'Count how many cycles PSEL is high while PENABLE is low.',
      explain: 'SETUP lasts two cycles here. It must last exactly one: PENABLE rises in the cycle after PSEL. Caught by <code>a_setup_to_access</code>.' },
    { title: 'PENABLE left behind', cfg: { ver: 3, txns: [{ write: 0, addr: 0x48, data: 0x5A5A5A5A, wait: 1 }] }, mutate: MUT.enAlone,
      hint: 'Check the cycle right after the transfer completes.',
      explain: 'The requester drops PSEL but leaves PENABLE high for a cycle. PENABLE must never be high without PSEL, and it must drop after completion. Caught by <code>a_en_needs_sel</code> and <code>a_en_drop</code>.' }
  ];
  PUZZLES.forEach(p => { p.wave = generate(clone(p.cfg)); p.mutate(p.wave); });

  /* Bugs for the lab's "Insert a bug" mode. Each one: a realistic cause,
     the buggy line, the waveform mutation, the assertion that catches it,
     two assertions that do NOT fire (for the guess), and the fix. */
  const BUGS = [
    { id: 'addr-wander', who: 'Requester', tag: 'Rule 2', title: 'Address moves during a wait state',
      story: 'The bridge copies the fast-bus address onto PADDR every clock. When the next request arrives during a wait state, PADDR follows it.',
      code: 'always_ff @(posedge PCLK) PADDR <= ahb_haddr;   // updated every clock',
      fix: 'Register PADDR only when the bus enters SETUP.', fixCode: 'always_ff @(posedge PCLK) if (nxt == SETUP) PADDR <= req_addr;',
      catches: 'a_stable_ctrl', decoys: ['a_en_drop', 'a_setup_to_access'], cfg: PUZZLES[0].cfg, mutate: MUT.addrWander },
    { id: 'no-setup', who: 'Requester', tag: 'Rule 1', title: 'No SETUP phase',
      story: 'The driver raises PSEL and PENABLE in the same clock, so the completer never sees a SETUP cycle.',
      code: 'vif.cb.PSEL <= 1;  vif.cb.PENABLE <= 1;   // same clock',
      fix: 'Drive PENABLE one clock after PSEL.', fixCode: 'vif.cb.PSEL <= 1;  vif.cb.PENABLE <= 0;\n@(vif.cb);\nvif.cb.PENABLE <= 1;',
      catches: 'a_rose_en_after_setup', decoys: ['a_en_needs_sel', 'a_stable_wdata'], cfg: { ver: 3, txns: [{ write: 0, addr: 0x08, data: 0xCAFE0001, wait: 1 }] }, mutate: MUT.noSetup },
    { id: 'give-up', who: 'Requester', tag: 'Rule 2', title: 'Driver gives up before PREADY',
      story: 'The driver waits exactly one ACCESS cycle and then drops PSEL, assuming every completer is zero-wait.',
      code: '@(vif.cb);  vif.cb.PSEL <= 0;  vif.cb.PENABLE <= 0;   // no PREADY loop',
      fix: 'Stay in ACCESS until the completer is ready.', fixCode: "do @(vif.cb); while (vif.cb.PREADY !== 1'b1);",
      catches: 'a_wait_hold', decoys: ['a_stable_ctrl', 'a_psel_onehot'], cfg: PUZZLES[2].cfg, mutate: MUT.giveUp },
    { id: 'en-stuck', who: 'Requester', tag: 'Rule 4', title: 'PENABLE stays high between transfers',
      story: 'For back-to-back transfers the requester only clears PENABLE when going idle, so the second transfer never gets a SETUP cycle.',
      code: "if (done && !req_valid) PENABLE <= 1'b0;   // never cleared for back-to-back",
      fix: 'Drive PENABLE from the state machine: high only in ACCESS.', fixCode: 'assign PENABLE = (state == ACCESS);',
      catches: 'a_en_drop', decoys: ['a_en_needs_sel', 'a_no_x_ctrl'], cfg: PUZZLES[3].cfg, mutate: MUT.enStuck },
    { id: 'wdata-change', who: 'Requester', tag: 'Rule 2', title: 'Write data changes mid-transfer',
      story: 'PWDATA is wired straight to a FIFO head. The FIFO pops on its own while the completer is still waiting, so the data changes underneath it.',
      code: 'assign PWDATA = wr_fifo.head;   // head moves when the FIFO pops',
      fix: 'Capture write data into a register at SETUP and hold it.', fixCode: 'always_ff @(posedge PCLK) if (nxt == SETUP) PWDATA <= wr_fifo.head;',
      catches: 'a_stable_wdata', decoys: ['a_stable_ctrl', 'a_no_x_wdata'], cfg: PUZZLES[5].cfg, mutate: MUT.wdataChange },
    { id: 'two-psel', who: 'Requester', tag: 'Decoder', title: 'Two completers selected at once',
      story: 'Two address ranges in the decoder overlap, so an address in 0x1000–0x1FFF raises both PSEL1 and PSEL2.',
      code: "assign PSEL1 = PSEL && (PADDR <  32'h2000);\nassign PSEL2 = PSEL && (PADDR >= 32'h1000);   // overlaps PSEL1",
      fix: 'Make decode ranges disjoint, and add a default completer for gaps.', fixCode: "assign PSEL1 = PSEL && (PADDR >= 32'h1000) && (PADDR < 32'h2000);\nassign PSEL2 = PSEL && (PADDR >= 32'h2000) && (PADDR < 32'h3000);",
      catches: 'a_psel_onehot', decoys: ['a_en_needs_sel', 'a_no_x_rdata'], cfg: { ver: 3, txns: [{ slave: 1, write: 1, addr: 0x1000, data: 0x0000CAFE, wait: 1, gap: 0 }, { slave: 2, write: 0, addr: 0x2000, data: 0x0000BEEF }] }, mutate: MUT.overlapSel },
    { id: 'en-alone', who: 'Requester', tag: 'Rule 3', title: 'PENABLE without PSEL',
      story: 'The requester clears PSEL on completion but clears PENABLE from a delayed copy of the done flag, one clock late.',
      code: 'if (done)   PSEL    <= 0;\nif (done_q) PENABLE <= 0;   // one clock late',
      fix: 'Derive both from one state register so they cannot drift apart.', fixCode: 'assign PSEL    = (state != IDLE);\nassign PENABLE = (state == ACCESS);',
      catches: 'a_en_needs_sel', decoys: ['a_wait_hold', 'a_stable_ctrl'], cfg: PUZZLES[9].cfg, mutate: MUT.enAlone },
    { id: 'long-setup', who: 'Requester', tag: 'Rule 1', title: 'SETUP lasts two cycles',
      story: 'The requester has an extra DECODE state that also drives PSEL, so PSEL is high for two clocks before PENABLE rises.',
      code: '// IDLE -> DECODE -> SETUP -> ACCESS\nassign PSEL = (state != IDLE);   // includes DECODE',
      fix: 'Decode before raising PSEL, so SETUP is exactly one clock.', fixCode: 'assign PSEL = (state == SETUP) || (state == ACCESS);',
      catches: 'a_setup_to_access', decoys: ['a_rose_en_after_setup', 'a_stable_ctrl'], cfg: PUZZLES[8].cfg, mutate: MUT.longSetup },
    { id: 'rdata-x', who: 'Completer', tag: 'Rule 5', title: 'Read data is X at completion',
      story: 'The read mux selects a status register that has no reset, so the first read returns X.',
      code: 'logic [31:0] status_q;      // no reset\nassign PRDATA = status_q;',
      fix: 'Reset every readable register.', fixCode: "always_ff @(posedge PCLK or negedge PRESETn)\n  if (!PRESETn) status_q <= '0;\n  else          status_q <= status_d;",
      catches: 'a_no_x_rdata', decoys: ['a_no_x_err', 'a_en_drop'], cfg: PUZZLES[6].cfg, mutate: MUT.rdataX },
    { id: 'err-early', who: 'Completer', tag: 'Rule 5', title: 'PSLVERR high before completion',
      story: 'PSLVERR comes straight from the address decoder, so it is high in SETUP and every wait state, not only at the triple-high edge.',
      code: 'assign PSLVERR = !addr_hit;',
      fix: 'Qualify the error with the completing cycle.', fixCode: 'assign PSLVERR = PSEL && PENABLE && PREADY && !addr_hit;',
      note: 'This one is only a warning. The specification recommends driving PSLVERR low outside completion but does not require it, so a correct requester simply ignores it there.',
      catches: 'a_err_only_on_done', decoys: ['a_no_x_err', 'a_wait_hold'], cfg: { ver: 3, txns: [{ write: 1, addr: 0xFF0, data: 0x1, wait: 2, err: 1 }] }, mutate: MUT.errEarly },
    { id: 'ready-x', who: 'Completer', tag: 'X-check', title: 'PREADY is X during wait states',
      story: 'PREADY comes from a flop with no reset, so it is X until the completer finishes its first access.',
      code: 'always_ff @(posedge PCLK) pready_q <= ready_next;   // no reset',
      fix: 'Give the flop a reset value.', fixCode: "always_ff @(posedge PCLK or negedge PRESETn)\n  if (!PRESETn) pready_q <= 1'b0;\n  else          pready_q <= ready_next;",
      catches: 'a_no_x_ready', decoys: ['a_no_x_rdata', 'a_en_drop'], cfg: { ver: 3, txns: [{ write: 1, addr: 0x24, data: 0x0000ABCD, wait: 2 }] }, mutate: MUT.readyX },
    { id: 'strb-read', who: 'Testbench', tag: 'APB4', title: 'Read sent with byte strobes', constraint: true,
      story: 'The sequence item randomises strb freely. Nothing ties it to the direction, so reads go out with strobes set.',
      code: 'rand bit [3:0] strb;   // no constraint linking strb to dir',
      fix: 'Add the protocol rule to the item as a hard constraint.', fixCode: "constraint c_strb_read { dir == APB_READ -> strb == 4'b0000; }",
      catches: 'a_strb_read', decoys: ['a_stable_wdata', 'a_no_x_wdata'],
      cfg: { ver: 4, txns: [{ write: 1, addr: 0x10, data: 0x000055AA, strb: 15, gap: 0 }, { write: 0, addr: 0x10, data: 0x000055AA, strb: 11, wait: 1 }] },
      clean: { ver: 4, txns: [{ write: 1, addr: 0x10, data: 0x000055AA, strb: 15, gap: 0 }, { write: 0, addr: 0x10, data: 0x000055AA, strb: 0, wait: 1 }] } },
    { id: 'pprot-x', who: 'Testbench', tag: 'X-check', title: 'PPROT left undriven', constraint: true,
      story: 'An APB3 driver was reused on an APB4 bus. It drives every signal it knows, but never PPROT, so PPROT stays X.',
      code: '// APB3 driver: drives PADDR, PWRITE, PWDATA, PSTRB ... but not PPROT',
      fix: 'Randomise a prot field in the item, drive it, and cover all eight values.', fixCode: 'rand bit [2:0] prot;          // in apb_txn\nvif.cb.PPROT <= t.prot;       // in the driver',
      catches: 'a_no_x_ctrl', decoys: ['a_strb_read', 'a_stable_ctrl'], cfg: { ver: 4, txns: [{ write: 1, addr: 0x30, data: 0x00001234, wait: 1, prot: 2 }] }, mutate: MUT.protX },
    { id: 'wait-unbounded', who: 'Testbench', tag: 'Policy', title: 'Completer model stalls forever', constraint: true,
      story: 'The reactive completer model randomises wait_cycles with no upper bound, so one transfer stalls for 20 cycles and the bridge times out.',
      code: 'rand int unsigned wait_cycles;   // no constraint',
      fix: 'Bound the wait states and weight the interesting values.', fixCode: 'constraint c_wait { wait_cycles dist { 0 := 45, [1:3] :/ 35, [4:15] :/ 17, 16 := 3 }; }',
      note: 'APB itself allows any number of wait states. This assertion is a testbench policy that should match your system bus timeout.',
      catches: 'a_max_wait', decoys: ['a_wait_hold', 'a_no_x_ready'],
      cfg: { ver: 3, txns: [{ write: 0, addr: 0x70, data: 0x99, wait: 20 }] }, clean: { ver: 3, txns: [{ write: 0, addr: 0x70, data: 0x99, wait: 3 }] } }
  ];
  function bugWave(b) { const w = generate(clone(b.cfg)); if (b.mutate) b.mutate(w); return w; }

  const QUIZ = [
    { l: 'b', q: 'What is the minimum number of PCLK cycles for one APB transfer?', o: ['1', '2', '3', '4'], a: 1, e: 'One SETUP cycle plus one ACCESS cycle. When PREADY is low, ACCESS stretches with wait states.' },
    { l: 'b', q: 'Which combination identifies the SETUP phase?', o: ['PSEL=1, PENABLE=0', 'PSEL=1, PENABLE=1', 'PSEL=0, PENABLE=1', 'PSEL=0, PENABLE=0'], a: 0, e: 'SETUP selects the completer (PSEL high) with PENABLE low. PSEL=0 with PENABLE=1 is never legal.' },
    { l: 'b', q: 'Which version introduced PREADY and PSLVERR?', o: ['APB2 (AMBA 2)', 'APB3 (AMBA 3)', 'APB4 (AMBA 4)', 'APB5 (AMBA 5)'], a: 1, e: 'APB3 added wait states (PREADY) and the error response (PSLVERR). In APB2 every transfer takes exactly two cycles.' },
    { l: 'b', q: 'Which signals did APB4 add?', o: ['PREADY and PSLVERR', 'PPROT and PSTRB', 'PWAKEUP and PAUSER', 'PSELx and PENABLE'], a: 1, e: 'APB4 added protection (PPROT) and byte-lane write strobes (PSTRB).' },
    { l: 'b', q: 'Who drives PREADY?', o: ['The requester (bridge)', 'The completer (peripheral)', 'The clock controller', 'The address decoder'], a: 1, e: 'The completer drives PREADY low to insert wait states and high to finish the transfer.' },
    { l: 'b', q: 'Which of these is NOT an APB feature?', o: ['Wait states', 'Burst transfers', 'Byte strobes (APB4)', 'Error response (APB3)'], a: 1, e: 'APB has no bursts, no pipelining and no outstanding transactions. Every transfer is a separate SETUP plus ACCESS.' },
    { l: 'b', q: 'With zero wait states, what is APB\'s best-case throughput?', o: ['One transfer per cycle', 'One transfer every 2 cycles', 'One transfer every 3 cycles', 'It depends on PPROT'], a: 1, e: 'Each transfer needs SETUP and ACCESS, so at best half of all cycles complete a transfer.' },
    { l: 'i', q: 'When is PSLVERR considered valid?', o: ['Whenever PSEL is high', 'In the SETUP phase', 'Only in the last cycle, when PSEL, PENABLE and PREADY are all high', 'One cycle after PREADY'], a: 2, e: 'PSLVERR is only sampled at the triple-high edge. Driving it low at other times is recommended, not required.' },
    { l: 'i', q: 'During an APB4 read transfer, PSTRB must be:', o: ['All ones', 'All zeros', 'Equal to the last write\'s strobes', 'Don\'t care'], a: 1, e: 'PSTRB only applies to writes and must be driven low for reads.' },
    { l: 'i', q: 'Two back-to-back transfers go to the same peripheral. Between them:', o: ['PSEL drops for one cycle', 'PSEL stays high and PENABLE drops for one SETUP cycle', 'PSEL and PENABLE both stay high', 'An IDLE cycle is mandatory'], a: 1, e: 'From ACCESS with PREADY high and another transfer pending, the bus goes straight to SETUP: PSEL stays high, PENABLE goes low.' },
    { l: 'i', q: 'PPROT = 3\'b011 means:', o: ['Normal, secure, data', 'Privileged, non-secure, data', 'Privileged, secure, instruction', 'Normal, non-secure, instruction'], a: 1, e: 'PPROT[0]=1 is privileged, PPROT[1]=1 is non-secure, PPROT[2]=0 is a data access.' },
    { l: 'i', q: 'A completer drives PREADY high during the SETUP phase. What happens?', o: ['The transfer completes in one cycle', 'It is a protocol violation', 'Nothing: PREADY is only sampled in ACCESS', 'The transfer is aborted'], a: 2, e: 'PREADY is a don\'t-care in SETUP. A completer that defaults PREADY high is legal and gives zero-wait transfers.' },
    { l: 'i', q: 'A read has 3 wait states. How many cycles from SETUP to completion, inclusive?', o: ['3', '4', '5', '6'], a: 2, e: '1 SETUP + 3 wait cycles + 1 completing ACCESS cycle = 5.' },
    { l: 'i', q: 'Which signals must stay stable from SETUP until the transfer completes?', o: ['Only PADDR', 'PSEL, PADDR, PWRITE, PWDATA for writes, plus PPROT and PSTRB in APB4', 'PRDATA and PREADY', 'None; only the completing edge matters'], a: 1, e: 'Everything the requester presents in SETUP holds through every wait state until PREADY is high.' },
    { l: 'i', q: 'A write completes with PSLVERR = 1. What can the scoreboard assume about the register?', o: ['It was definitely not written', 'It was definitely written', 'It may or may not have been updated', 'It was reset'], a: 2, e: 'The specification does not guarantee the peripheral state after a failed write. A robust scoreboard marks that register as unknown or uses design-specific rules.' },
    { l: 'i', q: 'A read completes with PSLVERR = 1. What should the scoreboard do with PRDATA?', o: ['Compare it as usual', 'Expect all zeros', 'Skip the comparison; the data is not guaranteed valid', 'Expect all ones'], a: 2, e: 'Read data is not required to be valid on an error response, so comparing it creates false failures.' },
    { l: 'a', q: 'Which SVA correctly checks that SETUP lasts exactly one cycle?', o: ['`(PSEL && !PENABLE) |-> (PSEL && PENABLE)`', '`(PSEL && !PENABLE) |=> (PSEL && PENABLE)`', '`PSEL |=> PENABLE`', '`$rose(PSEL) |-> PENABLE`'], a: 1, e: 'The non-overlapping implication checks the next cycle. Option A contradicts itself in the same cycle; C fails on back-to-back transfers; D requires PENABLE high in SETUP, which is wrong.' },
    { l: 'a', q: 'Why is `PSLVERR |-> (PSEL && PENABLE && PREADY)` usually reported with $warning?', o: ['SVA cannot check PSLVERR', 'Driving PSLVERR low outside completion is a recommendation, not a rule', 'It always fails at reset', 'PSLVERR is optional in APB4'], a: 1, e: 'A completer may leave PSLVERR high outside the completing cycle without breaking the protocol, so it is a lint-style warning.' },
    { l: 'a', q: 'In a UVM monitor, at which clock edge do you capture a completed transfer?', o: ['When PSEL rises', 'When PENABLE rises', 'When PSEL, PENABLE and PREADY are all high', 'When PREADY rises, regardless of PENABLE'], a: 2, e: 'Only the triple-high edge has valid PRDATA and PSLVERR. Sampling earlier records wait-state garbage or duplicates.' },
    { l: 'a', q: 'A driver waits exactly one cycle in ACCESS, then drops PSEL. Which completer exposes the bug?', o: ['One with PREADY tied high', 'One that inserts wait states', 'One that never errors', 'One with 8-bit data'], a: 1, e: 'With zero-wait completers the bug is invisible. Randomised wait states are what make a driver prove it loops on PREADY.' },
    { l: 'a', q: 'Which constraint prevents illegal APB4 stimulus?', o: ['`strb != 0`', '`dir == APB_READ -> strb == 0`', '`addr[1:0] != 0`', '`solve strb before dir`'], a: 1, e: 'Reads must carry PSTRB = 0. A write with PSTRB = 0 is legal, so `strb != 0` would remove a valid corner case.' },
    { l: 'a', q: 'An APB4 requester writes with PSTRB = 4\'b0001 to an APB3 completer. What is the risk?', o: ['None; APB3 completers decode PSTRB', 'The APB3 completer has no PSTRB, so it writes all 32 bits', 'The transfer gets PSLVERR automatically', 'The bridge turns it into a burst'], a: 1, e: 'Without PSTRB the completer writes the whole word, corrupting the other three bytes. The interconnect must block, error or emulate such writes.' },
    { l: 'a', q: 'What does PWAKEUP (APB5) signal?', o: ['A completer interrupt', 'Requester activity, so a completer can ungate clocks before PSEL', 'The end of reset', 'A parity error'], a: 1, e: 'PWAKEUP lets a power-managed completer wake ahead of the transfer. It should be glitch-free and asserted before or with PSEL.' },
    { l: 'a', q: 'APB5 interface protection (check) signals use:', o: ['Even parity across the whole bus', 'Odd parity, one check bit per byte or per signal group', 'ECC SECDED', 'CRC-8'], a: 1, e: 'Each *CHK signal carries odd parity over a byte of a wide signal or over a control group.' },
    { l: 'a', q: 'How do you cover back-to-back transfers most directly?', o: ['`cover property (done ##1 setup)` or transition bins on consecutive transfers', 'A coverpoint on PADDR', 'Counting PCLK cycles', 'Checking PRDATA != 0'], a: 0, e: 'A sequence cover hits it at the signal level, and transition bins (with idle_cycles == 0) hit it at the transaction level.' },
    { l: 'a', q: 'With `default disable iff (!PRESETn)`, how do you check that PSEL is low during reset?', o: ['As usual; disable iff handles it', 'Give that one assertion its own `disable iff (1\'b0)` so it is active in reset', 'It cannot be written in SVA', 'Use `$past(PRESETn)` only'], a: 1, e: 'The default disable condition would switch the check off exactly when it should run, so that assertion overrides it.' }
  ];

  const CHECKPOINT = [
    { q: 'A transfer has no wait states. How many clock cycles does it take?', o: ['1', '2', '3'], a: 1, e: 'One SETUP cycle and one ACCESS cycle. Always at least two.' },
    { q: 'In which phase is PENABLE high?', o: ['SETUP', 'ACCESS', 'IDLE'], a: 1, e: 'PENABLE is low in SETUP and high in ACCESS. That is its whole job: it says "now".' },
    { q: 'The completer holds PREADY low. What does the requester do?', o: ['Retry the transfer', 'Hold everything and wait', 'Drop PSEL and move on'], a: 1, e: 'It keeps PSEL, PENABLE, address and data frozen until PREADY goes high. APB has no retry and no abort.' }
  ];

  const STAGES = [
    { n: 1, name: 'Understand', what: 'What APB is and how one transfer works.' },
    { n: 2, name: 'See it', what: 'Watch, build and break real waveforms.' },
    { n: 3, name: 'Verify it', what: 'Rules, bugs, and the assertions that catch them.' },
    { n: 4, name: 'Prove it', what: 'Practice until it sticks.' }
  ];
  const CHAPTERS = [
    { id: 'basics', name: 'Basics', stage: 1, min: 4, rem: 'One requester, many completers. Every transfer is SETUP, then ACCESS.' },
    { id: 'signals', name: 'Signals', stage: 1, min: 6, rem: 'PSEL says who. PENABLE says now. PREADY says done.' },
    { id: 'fsm', name: 'State machine', stage: 1, min: 8, rem: 'SETUP is always one cycle. ACCESS repeats until PREADY is high.' },
    { id: 'checkpoint', name: 'Checkpoint', stage: 1, min: 2 },
    { id: 'lab', name: 'Waveform lab', stage: 2, min: 15, rem: 'Everything set in SETUP stays frozen until the triple-high edge.' },
    { id: 'versions', name: 'Versions', stage: 2, min: 10, rem: 'APB3 waits. APB4 protects. APB5 wakes up.' },
    { id: 'rules', name: 'Protocol rules', stage: 3, min: 5, rem: 'One SETUP. Freeze till READY. ENABLE needs SELECT. Drop ENABLE after. Sample at triple-high.' },
    { id: 'corner', name: 'Corner cases', stage: 3, min: 8, rem: 'Zero waits, many waits, back-to-back, errors, strobes, reset: hit each one on purpose.' },
    { id: 'bugs', name: 'Common bugs', stage: 3, min: 6, rem: 'If it only works with zero wait states, it does not work.' },
    { id: 'sva', name: 'Assertions', stage: 3, min: 10, rem: '|-> checks the same clock, |=> the next one. Disable on reset, except the reset check.' },
    { id: 'constraints', name: 'Constraints', stage: 3, min: 8, rem: 'Constrain the rules. Weight the corners.' },
    { id: 'coverage', name: 'Coverage', stage: 3, min: 6, rem: 'Sample coverage in the monitor, after the transfer completes.' },
    { id: 'tb', name: 'Reference TB', stage: 3, min: 7, rem: 'Drive through clocking blocks, loop on PREADY, sample at the triple-high edge.' },
    { id: 'drill', name: 'Draw it', stage: 4, min: 10, rem: 'If you can draw it from memory, you know it.' },
    { id: 'exercises', name: 'Exercises', stage: 4, min: 25 },
    { id: 'quiz', name: 'Quiz', stage: 4, min: 10 }
  ];

  /* ================================================================
     5b. Assertion builder model: conditions you can combine
     ================================================================ */
  const C_ = (w, i) => w.cycles[i];
  const COND = {
    setup:     { sv: 'setup_ph', txt: 'the bus is in SETUP', f: (w, f, i) => f[i].setup },
    wait:      { sv: 'wait_ph', txt: 'the bus is in a wait state', f: (w, f, i) => f[i].wait },
    sw:        { sv: '(setup_ph || wait_ph)', txt: 'the bus is in SETUP or a wait state', f: (w, f, i) => f[i].setup || f[i].wait },
    done:      { sv: 'done_ph', txt: 'it is the triple-high edge', f: (w, f, i) => f[i].done },
    access:    { sv: 'access_ph', txt: 'the bus is in ACCESS', f: (w, f, i) => f[i].access },
    sel:       { sv: '|PSELx', txt: 'PSEL is high', f: (w, f, i) => f[i].sel },
    nsel:      { sv: '!(|PSELx)', txt: 'PSEL is low', f: (w, f, i) => !f[i].sel },
    en:        { sv: 'PENABLE', txt: 'PENABLE is high', f: (w, f, i) => C_(w, i).PENABLE === 1 },
    nen:       { sv: '!PENABLE', txt: 'PENABLE is low', f: (w, f, i) => C_(w, i).PENABLE !== 1 },
    roseen:    { sv: '$rose(PENABLE)', txt: 'PENABLE rises', f: (w, f, i) => i > 0 && C_(w, i - 1).PENABLE !== 1 && C_(w, i).PENABLE === 1 },
    rosesel:   { sv: '$rose(|PSELx)', txt: 'PSEL rises', f: (w, f, i) => i > 0 && !f[i - 1].sel && f[i].sel },
    rd:        { sv: '(|PSELx && !PWRITE)', txt: 'a read is selected', f: (w, f, i) => f[i].sel && C_(w, i).PWRITE === 0 },
    wr:        { sv: '(|PSELx && PWRITE)', txt: 'a write is selected', f: (w, f, i) => f[i].sel && C_(w, i).PWRITE === 1 },
    rddone:    { sv: '(done_ph && !PWRITE && !PSLVERR)', txt: 'a read completes without error', f: (w, f, i) => f[i].done && C_(w, i).PWRITE === 0 && C_(w, i).PSLVERR !== 1 },
    err:       { sv: 'PSLVERR', txt: 'PSLVERR is high', f: (w, f, i) => C_(w, i).PSLVERR === 1 },
    nerr:      { sv: '!PSLVERR', txt: 'PSLVERR is low', f: (w, f, i) => C_(w, i).PSLVERR !== 1 },
    rdy:       { sv: 'PREADY', txt: 'PREADY is high', f: (w, f, i) => rdy(w, C_(w, i)) === 1 },
    rst:       { sv: '!PRESETn', txt: 'reset is asserted', reset: true, f: (w, f, i) => C_(w, i).PRESETn === 0 },
    always:    { sv: "1'b1", txt: 'any clock', f: () => true },
    idle:      { sv: '(!(|PSELx) && !PENABLE)', txt: 'PSEL and PENABLE are both low', f: (w, f, i) => !f[i].sel && C_(w, i).PENABLE !== 1 },
    pastsetup: { sv: '$past(setup_ph)', txt: 'the previous clock was SETUP', f: (w, f, i) => i > 0 && f[i - 1].setup },
    staddr:    { sv: '$stable(PADDR)', txt: 'PADDR has not changed', f: (w, f, i) => i > 0 && C_(w, i).PADDR === C_(w, i - 1).PADDR },
    stwd:      { sv: '$stable(PWDATA)', txt: 'PWDATA has not changed', f: (w, f, i) => i > 0 && C_(w, i).PWDATA === C_(w, i - 1).PWDATA },
    stsel:     { sv: '$stable(PSELx)', txt: 'the same PSEL is still selected', f: (w, f, i) => i > 0 && f[i].sv === f[i - 1].sv },
    strb0:     { sv: "(PSTRB == '0)", txt: 'PSTRB is 0000', ver: 4, f: (w, f, i) => w.ver < 4 || C_(w, i).PSTRB === 0 },
    noxrd:     { sv: '!$isunknown(PRDATA)', txt: 'PRDATA is not X', f: (w, f, i) => !isX(C_(w, i).PRDATA) },
    wake:      { sv: 'PWAKEUP', txt: 'PWAKEUP is high', ver: 5, f: (w, f, i) => w.ver < 5 || C_(w, i).PWAKEUP === 1 },
    onehot:    { sv: '$onehot0(PSELx)', txt: 'at most one PSEL is high', f: (w, f, i) => w.sels.filter(s => C_(w, i)[s] === 1).length <= 1 }
  };
  const B_ANTE = ['setup', 'wait', 'sw', 'access', 'done', 'sel', 'en', 'roseen', 'rosesel', 'rd', 'wr', 'rddone', 'err', 'rst', 'always'];
  const B_CONS = ['access', 'setup', 'en', 'nen', 'sel', 'nsel', 'idle', 'pastsetup', 'staddr', 'stwd', 'stsel', 'done', 'rdy', 'nerr', 'strb0', 'noxrd', 'wake', 'onehot'];
  const B_LIB = {
    'setup|=>access': 'a_setup_to_access', 'roseen|->pastsetup': 'a_rose_en_after_setup', 'wait|=>access': 'a_wait_hold',
    'sw|=>staddr': 'a_stable_ctrl', 'sw|=>stwd': 'a_stable_wdata', 'done|=>nen': 'a_en_drop', 'en|->sel': 'a_en_needs_sel',
    'rd|->strb0': 'a_strb_read', 'err|->done': 'a_err_only_on_done', 'rddone|->noxrd': 'a_no_x_rdata', 'rst|->idle': 'a_reset_idle',
    'sel|->wake': 'a_wake_during_xfer', 'always|->onehot': 'a_psel_onehot', 'wait|=>stsel': 'a_wait_hold', 'setup|=>stsel': 'a_setup_to_access'
  };
  function evalCustom(w, a, op, c) {
    const f = flags(w), n = f.length, A = COND[a], K = COND[c], rm = !!A.reset, r = { att: [], fails: [] };
    for (let i = 0; i < n; i++) {
      if (!rm && !f[i].live) continue;
      if (!A.f(w, f, i)) continue;
      const j = op === '|=>' ? i + 1 : i;
      if (j >= n || (!rm && !f[j].live)) continue;
      r.att.push(i);
      if (!K.f(w, f, j)) r.fails.push({ i: j, from: i, msg: `Expected “${K.txt}” at T${j + 1}, but it is not.` });
    }
    return r;
  }
  function customSVA(a, op, c) {
    const A = COND[a], K = COND[c];
    return A.reset ? `a_my_check: assert property (@(posedge PCLK) disable iff (1'b0)\n  ${A.sv} ${op} ${K.sv});`
      : `a_my_check: assert property (${A.sv} ${op} ${K.sv});`;
  }
  const B_CHALLENGES = [
    { bug: 'addr-wander', hint: 'When the bus is in SETUP or a wait state, what must be true about PADDR one clock later?' },
    { bug: 'no-setup', hint: 'When PENABLE rises, what must the previous clock have been?' },
    { bug: 'en-stuck', hint: 'What must PENABLE do in the clock after the triple-high edge?' },
    { bug: 'en-alone', hint: 'In the same clock: if PENABLE is high, what else must be high?' },
    { bug: 'give-up', hint: 'During a wait state, what must still be true one clock later?' },
    { bug: 'strb-read', hint: 'When a read is selected, what must PSTRB be? (APB4)' }
  ];

  /* ================================================================
     5c. Draw-it drills
     ================================================================ */
  const DRILLS = [
    { id: 'd1', lvl: 'b', title: 'APB2 write, no wait states', task: 'Draw an APB2 write. The transfer starts in cycle 1, after one IDLE cycle.', draw: ['PSEL', 'PENABLE'], cfg: { ver: 2, txns: [{ write: 1, addr: 0x10, data: 1 }] } },
    { id: 'd2', lvl: 'b', title: 'Read with two wait states', task: 'Draw an APB3 read with two wait states. The transfer starts in cycle 1.', draw: ['PSEL', 'PENABLE', 'PREADY'], cfg: { ver: 3, txns: [{ write: 0, addr: 0x14, data: 5, wait: 2 }] } },
    { id: 'd3', lvl: 'i', title: 'Write that ends in an error', task: 'Draw an APB3 write with one wait state that completes with an error. The transfer starts in cycle 1.', draw: ['PSEL', 'PENABLE', 'PREADY', 'PSLVERR'], cfg: { ver: 3, txns: [{ write: 1, addr: 0x20, data: 2, wait: 1, err: 1 }] } },
    { id: 'd4', lvl: 'i', title: 'Two writes, back-to-back', task: 'Draw two APB3 writes to the same peripheral with no wait states and no IDLE cycle between them. Start in cycle 1.', draw: ['PSEL', 'PENABLE', 'PREADY'], cfg: { ver: 3, txns: [{ write: 1, addr: 0x10, data: 1, gap: 0 }, { write: 1, addr: 0x14, data: 2 }] } },
    { id: 'd5', lvl: 'i', title: 'Read, a gap, then a write', task: 'Draw a read with one wait state, then one IDLE cycle, then a write with no wait states. Start in cycle 1. PWRITE only matters while PSEL is high.', draw: ['PSEL', 'PENABLE', 'PREADY', 'PWRITE'], cfg: { ver: 3, txns: [{ write: 0, addr: 0x10, data: 3, wait: 1, gap: 1 }, { write: 1, addr: 0x14, data: 4 }] } },
    { id: 'd6', lvl: 'a', title: 'Hand over to another peripheral', task: 'Draw a write to peripheral 1 with one wait state, immediately followed by a read from peripheral 2 with no wait states. Start in cycle 1.', draw: ['PSEL1', 'PSEL2', 'PENABLE', 'PREADY'], cfg: { ver: 3, txns: [{ slave: 1, write: 1, addr: 0x1000, data: 1, wait: 1, gap: 0 }, { slave: 2, write: 0, addr: 0x2000, data: 2 }] } },
    { id: 'd7', lvl: 'a', title: 'Out of reset', task: 'Reset is asserted in cycles 0 and 1. Draw PRESETn, then a read with no wait states that starts in cycle 3, after one IDLE cycle.', draw: ['PRESETn', 'PSEL', 'PENABLE', 'PREADY'], cfg: { ver: 3, reset: 2, idle: 1, txns: [{ write: 0, addr: 0x0, data: 1 }] } },
    { id: 'd8', lvl: 'a', title: 'APB5 wake-up', task: 'Draw an APB5 write with one wait state that starts in cycle 2. Raise PWAKEUP one cycle before PSEL and keep it high until the transfer completes.', draw: ['PWAKEUP', 'PSEL', 'PENABLE', 'PREADY'], cfg: { ver: 5, idle: 2, wake: 1, txns: [{ write: 1, addr: 0x50, data: 1, wait: 1 }] } }
  ];
  // A cell is "don't care" when APB never samples that signal in that cycle
  function drillDC(w, sig, i) {
    const ph = phaseOf(w, i);
    if (sig === 'PREADY') return ph !== 'WAIT' && ph !== 'ACCESS';
    if (sig === 'PSLVERR') return ph !== 'ACCESS';
    if (sig === 'PWRITE') return !anySel(w, w.cycles[i]);
    if (sig === 'PWAKEUP') { let last = -1; w.cycles.forEach((_, k) => { if (phaseOf(w, k) === 'ACCESS') last = k; }); return i > last; }
    return false;
  }
  function gradeDrill(d, user) {
    const w = generate(clone(d.cfg)), wrong = [], uw = clone(w);
    d.draw.forEach(s => w.cycles.forEach((c, i) => {
      const dc = drillDC(w, s, i), want = c[s] === 1 ? 1 : 0, got = user[s][i];
      if (!dc && want !== got) wrong.push({ s, i });
      if (!dc) uw.cycles[i][s] = got;
    }));
    const viol = check(uw).filter(v => v.sev === 'error');
    return { w, wrong, viol };
  }

  /* ================================================================
     5d. Voice guide scripts
     ================================================================ */
  const GUIDE = {
    top: 'Welcome to PosEdge, the A P B lab. APB is the simplest bus in the AMBA family, and you can learn the whole protocol here in under an hour. I will tell you what each section is about and how to use it. Press Next section to go to the roadmap.',
    roadmap: 'This is your roadmap. It has four stages: understand, see it, verify it, and prove it. Stages one and two teach the whole protocol in about forty-five minutes. Press the blue button to start or continue, and press Mark done at the end of each chapter to track your progress.',
    basics: 'Basics. This chapter gives you APB in three lines. PSEL says who, PENABLE says now, and PREADY says done. The transfer happens at the clock edge where all three are high, which this page calls the triple-high edge. Move your mouse across the first waveform and read the explanation under it, one clock cycle at a time.',
    signals: 'Signals. This table lists every APB signal, who drives it, and what to verify. Use the version buttons above the table to see which signals exist in APB two, three, four and five. Rows that are new in the chosen version are highlighted.',
    fsm: 'State machine. APB has only three states: idle, setup and access. Queue a write or a read, then press Clock edge to move one cycle at a time. Untick Completer ready to add wait states, and watch the waveform grow under the diagram.',
    checkpoint: 'Checkpoint. Three quick questions. If you get all three right, you understand the core of APB, and everything after this is detail.',
    lab: 'Waveform lab. This is the heart of the page. First, choose a scenario. Then use the three menus right above the waveform: apply an assertion, insert a bug, or switch on random stimulus. Whatever you pick is marked on the waveform and explained in the box right under it. The Go deeper tabs further down let you build your own assertion, set several constraints, or edit the waveform by hand.',
    versions: 'Versions. There is one card for each APB version, each with its own waveform. An easy way to remember them: APB three waits, APB four protects, and APB five wakes up. Press Open in lab on any card to explore more scenarios for that version.',
    rules: 'Protocol rules. Five rules cover almost everything: one cycle of setup, freeze until ready, enable needs select, drop enable after, and sample at the triple-high edge. Each rule card has a See it break button that loads a matching bug into the lab.',
    corner: 'Corner cases. These are the situations where real APB designs break, such as zero wait states, long stalls, back-to-back transfers and errors. Each card tells you why it matters and how to hit it in a testbench.',
    bugs: 'Common bugs. First the design bugs, then the testbench bugs. Each row shows the bug, its symptom, and what catches it. Read the testbench bugs carefully, because they hide design bugs.',
    sva: 'Assertions. This is a complete SystemVerilog checker that you can bind to any APB interface. Use the Copy button to take it into your own project. The notes below it explain the difference between same-clock and next-clock implication.',
    constraints: 'Constraints. This is the sequence item that generates legal APB stimulus. Hard constraints enforce protocol rules, and weighted distributions push tests into the corners. Try switching constraints off in the lab to see why each one exists.',
    coverage: 'Coverage. This covergroup proves that your tests reached the corners. Sample it in the monitor, after each transfer completes. The coverage plan below maps each feature to the bins that close it.',
    tb: 'Reference testbench. A small APB completer to verify, plus the interface, the driver and the monitor. The comments in the code point to the rule each line implements. At the end, open the full UVM environment for an APB RAM on EDA Playground, with a scoreboard, coverage and two tests you can run.',
    drill: 'Draw it. This is the interview drill. Read the task, then click the cells to draw each signal, cycle by cycle. Press Check to grade your waveform. Grey cells are do not care, because APB never samples that signal in that cycle.',
    exercises: 'Exercises. Start with the bug hunt: find the clock cycle where each waveform breaks the protocol. Then do the lab tasks and the written exercises. Each written exercise has a hint and a solution you can open when you are ready.',
    quiz: 'Quiz. Twenty-six questions from basic to advanced, each with an explanation. Pick a level, answer, and review the ones you missed. At the end, make your completion card to share your progress.'
  };

  /* ================================================================
     6. Constrained random (mirrors apb_txn in chapter 10) and coverage
     ================================================================ */
  const CONSTRAINTS = [
    { id: 'c_strb_read', ver: 4, code: "dir == APB_READ -> strb == 4'b0000;", plain: 'Reads always have PSTRB = 0000.', ifOff: 'Reads get random strobes and a_strb_read fails. This one is a protocol rule, so it must stay on.' },
    { id: 'c_strb_write', ver: 4, code: "dir == APB_WRITE -> strb dist { 4'hF := 60, [4'h1:4'hE] :/ 35, 4'h0 := 5 };", plain: 'Writes mostly use all four bytes, sometimes fewer, rarely none.', ifOff: 'Strobes become uniform, so full-word writes (1111) turn rare.' },
    { id: 'c_wait', ver: 3, code: 'wait_cycles dist { 0 := 45, [1:3] :/ 35, [4:15] :/ 17, 16 := 3 };', plain: 'Usually no wait, sometimes a few, rarely up to 16.', ifOff: `Waits go up to 24 with no bias. Stalls over ${MAX_WAIT} trip a_max_wait.` },
    { id: 'c_err', ver: 3, code: "slverr dist { 1'b0 := 90, 1'b1 := 10 };", plain: 'About one transfer in ten gets an error.', ifOff: 'Half of all transfers fail. Good for error coverage, bad for normal traffic.' },
    { id: 'c_aligned', ver: 2, code: "addr[1:0] == 2'b00;", plain: 'Addresses are multiples of 4.', ifOff: 'Unaligned addresses appear. No assertion fires: APB allows them, and your design spec decides.' },
    { id: 'c_in_range', ver: 2, code: 'addr inside {[base : base + size - 4]};   // 4 KB map', plain: 'Addresses stay inside the 4 KB register map.', ifOff: 'Addresses land outside the map, and the completer model answers them with PSLVERR.' },
    { id: 'c_idle', ver: 2, code: 'idle_cycles dist { 0 := 55, [1:2] :/ 30, [3:8] :/ 15 };', plain: 'Back-to-back transfers are common, long gaps are rare.', ifOff: 'Gaps of 0 to 8 cycles with no bias, so back-to-back gets rarer.' }
  ];
  const COVER = [
    { cp: 'cp_dir', ver: 2, bins: ['WRITE', 'READ'] },
    { cp: 'cp_wait', ver: 3, bins: ['0', '1', '2–3', '4–15', '16+'] },
    { cp: 'cp_err', ver: 3, bins: ['OKAY', 'ERROR'] },
    { cp: 'x_dir_err', ver: 3, bins: ['W·OK', 'W·ERR', 'R·OK', 'R·ERR'] },
    { cp: 'cp_strb', ver: 4, bins: ['1111', '0000', 'single', 'halves', 'sparse', 'three'] },
    { cp: 'cp_prot', ver: 4, bins: ['000', '001', '010', '011', '100', '101', '110', '111'] },
    { cp: 'cp_idle', ver: 2, bins: ['b2b', 'gap'] },
    { cp: 'cp_seq', ver: 2, bins: ['W→W', 'W→R', 'R→W', 'R→R'] }
  ];
  function mulberry32(a) {
    return function () {
      a |= 0; a = a + 0x6D2B79F5 | 0;
      let t = Math.imul(a ^ a >>> 15, 1 | a);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  }
  // dist with SystemVerilog semantics, driven by two pre-drawn uniforms so that
  // switching a constraint never shifts the random values of other fields
  function distU(u1, u2, spec) {
    const items = spec.map(([wt, lo, hi, k]) => ({ lo, hi, tot: k === ':=' ? wt * (hi - lo + 1) : wt }));
    let r = u1 * items.reduce((s, x) => s + x.tot, 0);
    for (const x of items) { if (r < x.tot) return x.lo + Math.floor(u2 * (x.hi - x.lo + 1)); r -= x.tot; }
    return items[items.length - 1].hi;
  }
  const DIST = {
    strb: [[60, 15, 15, ':='], [35, 1, 14, ':/'], [5, 0, 0, ':=']],
    wait: [[45, 0, 0, ':='], [35, 1, 3, ':/'], [17, 4, 15, ':/'], [3, 16, 16, ':=']],
    idle: [[55, 0, 0, ':='], [30, 1, 2, ':/'], [15, 3, 8, ':/']]
  };
  function randomize(seed, n, on, ver) {
    const rng = mulberry32(seed), items = [];
    for (let k = 0; k < n; k++) {
      const u = Array.from({ length: 14 }, () => rng());
      const dir = u[0] < 0.5 ? 1 : 0;
      const inRange = on.c_in_range || u[1] < 0.5;
      let addr = inRange ? Math.floor(u[2] * 1024) * 4 : ((1 + Math.floor(u[3] * 0xFFFFF)) * 0x1000 + Math.floor(u[2] * 1024) * 4) >>> 0;
      if (!on.c_aligned) addr = (addr + Math.floor(u[4] * 4)) >>> 0;
      const data = Math.floor(u[5] * 4294967296) >>> 0;
      let strb;
      if (ver >= 4) {
        if (dir) strb = on.c_strb_write ? distU(u[6], u[7], DIST.strb) : Math.floor(u[6] * 16);
        else strb = on.c_strb_read ? 0 : Math.floor(u[6] * 16);
      }
      const wait = ver >= 3 ? (on.c_wait ? distU(u[8], u[9], DIST.wait) : Math.floor(u[8] * 25)) : 0;
      let err = ver >= 3 ? ((on.c_err ? u[10] < 0.10 : u[10] < 0.5) ? 1 : 0) : 0;
      if (!inRange && ver >= 3) err = 1;   // a default completer answers unmapped addresses with an error
      const idle = on.c_idle ? distU(u[11], u[12], DIST.idle) : Math.floor(u[11] * 9);
      const prot = ver >= 4 ? Math.floor(u[13] * 8) : 0;
      items.push({ dir, addr, data, strb, wait, err, idle, prot, unmapped: !inRange });
    }
    return items;
  }
  function itemsToCfg(items, ver) {
    return {
      ver, idle: Math.max(1, items[0].idle),
      txns: items.map((it, k) => ({ write: it.dir, addr: it.addr, data: it.data, strb: ver >= 4 ? it.strb : undefined, prot: it.prot, wait: it.wait, err: it.err, gap: k < items.length - 1 ? items[k + 1].idle : 2 }))
    };
  }
  const waitBin = v => (v === 0 ? 0 : v === 1 ? 1 : v <= 3 ? 2 : v <= 15 ? 3 : 4);
  const strbBin = s => (s === 15 ? 0 : s === 0 ? 1 : [1, 2, 4, 8].includes(s) ? 2 : [3, 12].includes(s) ? 3 : [5, 10, 6, 9].includes(s) ? 4 : 5);
  function newCov() { return Object.fromEntries(COVER.map(c => [c.cp, c.bins.map(() => 0)])); }
  function sampleCov(cov, items, ver) {
    items.forEach((it, k) => {
      cov.cp_dir[it.dir ? 0 : 1]++;
      if (ver >= 3) { cov.cp_wait[waitBin(it.wait)]++; cov.cp_err[it.err]++; cov.x_dir_err[(it.dir ? 0 : 2) + it.err]++; }
      if (ver >= 4) { if (it.dir) cov.cp_strb[strbBin(it.strb)]++; cov.cp_prot[it.prot]++; }
      if (k > 0) { cov.cp_idle[it.idle ? 1 : 0]++; cov.cp_seq[(items[k - 1].dir ? 0 : 2) + (it.dir ? 0 : 1)]++; }
    });
  }

  /* ================================================================
     Node export for offline testing
     ================================================================ */
  if (typeof module !== 'undefined' && module.exports) {
    module.exports = { COND, evalCustom, customSVA, B_ANTE, B_CONS, B_CHALLENGES, DRILLS, drillDC, gradeDrill, GUIDE, generate, check, evalAll, phaseOf, explain, ASSERTS, PRESETS, PUZZLES, BUGS, bugWave, QUIZ, CHECKPOINT, CHAPTERS, randomize, itemsToCfg, newCov, sampleCov, COVER, CONSTRAINTS };
  }
  if (typeof document === 'undefined') return;

  /* ================================================================
     7. DOM helpers and storage
     ================================================================ */
  const $ = (s, r) => (r || document).querySelector(s);
  const $$ = (s, r) => Array.from((r || document).querySelectorAll(s));
  const mem = {};   // keeps progress for this visit when browser storage is blocked
  const store = {
    get(k, d) { if (k in mem) return mem[k]; try { const v = localStorage.getItem('apblab:' + k); return v == null ? d : JSON.parse(v); } catch (e) { return d; } },
    set(k, v) { mem[k] = v; try { localStorage.setItem('apblab:' + k, JSON.stringify(v)); } catch (e) { /* storage unavailable */ } }
  };
  const reduceMotion = !!(window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches);
  const scrollToId = id => { const el = document.getElementById(id); if (el && el.scrollIntoView) el.scrollIntoView({ behavior: reduceMotion ? 'auto' : 'smooth', block: 'start' }); };
  const shuffle = a => { a = a.slice(); for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; };
  let uid = 0;

  function runs(arr) {
    const r = [];
    arr.forEach((v, i) => {
      const last = r[r.length - 1];
      if (last && last.v === v) last.b = i; else r.push({ a: i, b: i, v });
    });
    return r;
  }

  /* ================================================================
     8. Waveform renderer
     ================================================================ */
  function Wave(host, opts) {
    opts = Object.assign({ cw: 52, compact: false, phase: true, showViol: true, edit: false, markBand: false }, opts || {});
    const id = 'wv' + (++uid);
    const self = { wave: null, viol: [], cursor: -1, locked: false, marks: null, focus: null, opts, onCell: null, onPick: null };
    const listeners = [];
    const box = document.createElement('div');
    box.className = 'wv-box' + (opts.compact ? ' compact' : '');
    const labels = document.createElement('div');
    labels.className = 'wv-labels';
    const scroll = document.createElement('div');
    scroll.className = 'wv-scroll';
    scroll.tabIndex = 0;
    scroll.setAttribute('role', 'group');
    scroll.setAttribute('aria-label', 'Waveform. Hover or tap a cycle; left and right arrow keys move the cursor.');
    box.append(labels, scroll);
    host.appendChild(box);
    let G = null;
    const OFF = 12;

    self.on = fn => listeners.push(fn);
    const emit = () => listeners.forEach(fn => fn(self.cursor, self));

    self.set = function (w, keepCursor) {
      self.wave = w;
      self.viol = check(w);
      if (!keepCursor) { self.cursor = -1; self.locked = false; }
      if (self.cursor >= w.cycles.length) self.cursor = w.cycles.length - 1;
      draw(); emit();
    };
    self.setCW = cw => { opts.cw = cw; draw(); };
    self.setShowViol = v => { if (opts.showViol === v) return; opts.showViol = v; draw(); emit(); };
    self.setEdit = v => { opts.edit = v; box.classList.toggle('editing', v); };
    self.setMarks = m => { self.marks = m; draw(); };
    self.setCursor = function (i, lock) {
      if (!self.wave) return;
      self.cursor = Math.max(-1, Math.min(self.wave.cycles.length - 1, i));
      if (lock !== undefined) self.locked = lock;
      placeCursor(); emit();
    };
    self.ensureVisible = function () {
      if (!G || self.cursor < 0) return;
      const x = OFF + self.cursor * G.CW;
      if (x < scroll.scrollLeft) scroll.scrollLeft = x - 8;
      else if (x + G.CW > scroll.scrollLeft + scroll.clientWidth) scroll.scrollLeft = x + G.CW - scroll.clientWidth + 8;
    };
    self.scrollEnd = () => { scroll.scrollLeft = scroll.scrollWidth; };
    self.el = box;

    function violByCycle() {
      const m = new Map();
      self.viol.forEach(v => { if (m.get(v.i) !== 'error') m.set(v.i, v.sev); });
      return m;
    }

    function draw() {
      const w = self.wave; if (!w) return;
      const C = w.cycles, n = C.length, lanes = w.lanes;
      const LBL = opts.compact ? 76 : 92, CW = opts.cw, LH = opts.compact ? 26 : 30;
      const RUL = 20, MK = opts.markBand ? 18 : 0, PH = opts.phase ? 22 : 0, TOP = RUL + MK + PH + 4;
      const W = OFF + n * CW + 12, H = TOP + lanes.length * LH + 6;
      G = { CW, LH, RUL, PH, TOP, W, H, n };
      const X = i => OFF + i * CW;
      const SK = 3;
      const s = [], L = [];
      s.push(`<svg class="wv" xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}" aria-hidden="true">`);
      s.push(`<defs><pattern id="${id}h" width="5" height="5" patternUnits="userSpaceOnUse" patternTransform="rotate(45)"><line x1="0" y1="0" x2="0" y2="5" class="hatch-ln"/></pattern></defs>`);
      L.push(`<svg class="wv" xmlns="http://www.w3.org/2000/svg" width="${LBL}" height="${H}" viewBox="0 0 ${LBL} ${H}" aria-hidden="true">`);
      const vc = violByCycle();
      if (opts.showViol) vc.forEach((sev, i) => s.push(`<rect class="vband ${sev}" x="${X(i)}" y="${RUL}" width="${CW}" height="${H - RUL}"/>`));
      const FL = (self.focus && self.focus.lanes) || [];
      lanes.forEach((name, li) => { if (FL.includes(name)) { const y0 = TOP + li * LH; s.push(`<rect class="lane-hl" x="0" y="${y0}" width="${W}" height="${LH}"/>`); L.push(`<rect class="lane-hl" x="0" y="${y0}" width="${LBL}" height="${LH}"/>`); } });
      s.push(`<rect class="cur-band" x="0" y="${RUL}" width="${CW}" height="${H - RUL}" visibility="hidden"/>`);
      const every = CW >= 36 ? 1 : 2;
      for (let k = 0; k <= n; k++) {
        s.push(`<line class="grid" x1="${X(k)}" y1="${RUL}" x2="${X(k)}" y2="${H - 2}"/>`);
        if (k % every === 0) s.push(`<text class="tick" x="${X(k)}" y="${RUL - 7}">T${k}</text>`);
      }
      if (MK) {
        L.push(`<text class="lbl lbl-mk" x="10" y="${RUL + 13}">checks</text>`);
        const m = self.marks, my = RUL + 9;
        if (m) {
          (m.links || []).forEach(([a, b]) => s.push(`<line class="mk-link" x1="${X(a) + CW / 2 + 5}" x2="${X(b) + CW / 2 - 7}" y1="${my}" y2="${my}"/>`));
          (m.trig || []).forEach(i => s.push(`<circle class="mk-trig" cx="${X(i) + CW / 2}" cy="${my}" r="3.4"/>`));
          (m.fail || []).forEach(i => { const cx = X(i) + CW / 2; s.push(`<path class="mk-fail" d="M${cx - 4.5},${my - 4.5} L${cx + 4.5},${my + 4.5} M${cx + 4.5},${my - 4.5} L${cx - 4.5},${my + 4.5}"/>`); });
          (m.cur || []).forEach(i => s.push(`<circle class="mk-cur" cx="${X(i) + CW / 2}" cy="${my}" r="7.5"/>`));
        }
      }
      if (opts.phase) {
        const py = RUL + MK;
        runs(C.map((_, i) => phaseOf(w, i))).forEach(r => {
          const x1 = X(r.a) + 1.5, x2 = X(r.b + 1) - 1.5, lab = PHLABEL[r.v];
          s.push(`<rect class="ph ph-${r.v}" x="${x1}" y="${py + 3}" width="${x2 - x1}" height="${PH - 6}" rx="3"/>`);
          if (x2 - x1 > lab.length * 6.2 + 6) s.push(`<text class="ph-t" x="${(x1 + x2) / 2}" y="${py + PH / 2 + 3.5}">${lab}</text>`);
        });
        L.push(`<text class="lbl lbl-ph" x="10" y="${py + PH / 2 + 4}">phase</text>`);
      }
      lanes.forEach((name, li) => {
        const y0 = TOP + li * LH, hi = y0 + 5, lo = y0 + LH - 7, mid = (hi + lo) / 2;
        const grp = SIG[name].grp;
        L.push(`<text class="lbl g-${grp}${FL.includes(name) ? ' lbl-hl' : ''}" x="10" y="${mid + 4}">${name}</text>`);
        if (li) { s.push(`<line class="lane-sep" x1="0" x2="${W}" y1="${y0}" y2="${y0}"/>`); L.push(`<line class="lane-sep" x1="0" x2="${LBL}" y1="${y0}" y2="${y0}"/>`); }
        if (SIG[name].kind === 'clk') {
          let d = `M${X(0)},${lo}`;
          for (let i = 0; i < n; i++) { const x = X(i); d += `L${x},${hi}L${x + CW / 2},${hi}L${x + CW / 2},${lo}L${x + CW},${lo}`; }
          s.push(`<path class="tr g-clk" d="${d}"/>`);
          return;
        }
        const rr = runs(C.map(c => (c[name] === undefined ? 'x' : c[name])));
        const xs = r => (r.a === 0 ? X(0) : X(r.a) + SK);
        const xe = r => (r.b === n - 1 ? X(n) : X(r.b + 1) + SK);
        if (SIG[name].w === 1) {
          let prevY = null;
          rr.forEach(r => {
            const x1 = xs(r), x2 = xe(r);
            if (r.v === 0 || r.v === 1) {
              const y = r.v ? hi : lo;
              if (prevY !== null && prevY !== y) s.push(`<line class="tr g-${grp}" x1="${x1}" x2="${x1}" y1="${prevY}" y2="${y}"/>`);
              s.push(`<line class="tr g-${grp}" x1="${x1}" x2="${x2}" y1="${y}" y2="${y}"/>`);
              prevY = y;
            } else {
              s.push(`<rect class="xbox" x="${x1}" y="${hi}" width="${x2 - x1}" height="${lo - hi}" fill="url(#${id}h)"/>`);
              prevY = null;
            }
          });
        } else {
          rr.forEach(r => {
            const x1 = xs(r), x2 = xe(r), k = Math.min(4, (x2 - x1) / 2);
            const pts = `${x1},${mid} ${x1 + k},${hi} ${x2 - k},${hi} ${x2},${mid} ${x2 - k},${lo} ${x1 + k},${lo}`;
            if (isX(r.v)) { s.push(`<polygon class="bus bx" points="${pts}" fill="url(#${id}h)"/>`); return; }
            s.push(`<polygon class="bus g-${grp}" points="${pts}"/>`);
            const t = fmt(name, r.v);
            if ((x2 - x1) - 2 * k > t.length * 6.5 + 2) s.push(`<text class="bus-t g-${grp}" x="${(x1 + x2) / 2}" y="${mid + 3.8}">${t}</text>`);
          });
        }
      });
      if (self.focus && self.focus.cells) self.focus.cells.forEach(({ lane, i }) => { const li = lanes.indexOf(lane); if (li < 0 || i >= n) return; s.push(`<rect class="cell-diff${self.focus.kind === 'bug' ? ' bug' : ''}" x="${X(i) + 2}" y="${TOP + li * LH + 2}" width="${CW - 4}" height="${LH - 4}" rx="3"/>`); });
      if (opts.showViol) vc.forEach((sev, i) => { const cx = X(i) + CW / 2; s.push(`<path class="vmark ${sev}" d="M${cx - 5},${RUL - 18} L${cx + 5},${RUL - 18} L${cx},${RUL - 10} Z"/>`); });
      s.push(`<line class="cur-line" x1="0" x2="0" y1="${RUL - 4}" y2="${H - 2}" visibility="hidden"/>`);
      s.push(`<rect class="cell-hov" x="0" y="0" width="${CW}" height="${LH}" rx="3" visibility="hidden"/>`);
      s.push(`<rect class="hit" x="${X(0)}" y="0" width="${n * CW}" height="${H}"/>`);
      s.push('</svg>'); L.push('</svg>');
      scroll.innerHTML = s.join('');
      labels.innerHTML = L.join('');
      placeCursor();
    }

    function placeCursor() {
      const svg = scroll.firstChild; if (!svg || !G) return;
      const band = svg.querySelector('.cur-band'), line = svg.querySelector('.cur-line');
      if (self.cursor < 0) { band.setAttribute('visibility', 'hidden'); line.setAttribute('visibility', 'hidden'); return; }
      const x = OFF + self.cursor * G.CW;
      band.setAttribute('x', x); band.setAttribute('visibility', 'visible');
      band.setAttribute('class', 'cur-band' + (self.locked ? ' locked' : ''));
      line.setAttribute('x1', x + G.CW); line.setAttribute('x2', x + G.CW); line.setAttribute('visibility', 'visible');
    }

    function locate(e) {
      const svg = scroll.firstChild; if (!svg || !G || !self.wave) return null;
      const r = svg.getBoundingClientRect();
      const x = e.clientX - r.left, y = e.clientY - r.top;
      const i = Math.floor((x - OFF) / G.CW);
      if (i < 0 || i >= G.n) return null;
      const li = Math.floor((y - G.TOP) / G.LH);
      const lane = (li >= 0 && li < self.wave.lanes.length) ? self.wave.lanes[li] : null;
      return { i, li, lane };
    }
    scroll.addEventListener('pointermove', e => {
      const P = locate(e); const svg = scroll.firstChild; if (!svg) return;
      const hov = svg.querySelector('.cell-hov');
      if (opts.edit && P && P.lane && P.lane !== 'PCLK') {
        hov.setAttribute('x', OFF + P.i * G.CW); hov.setAttribute('y', G.TOP + P.li * G.LH); hov.setAttribute('visibility', 'visible');
      } else hov.setAttribute('visibility', 'hidden');
      if (!P || self.locked) return;
      if (P.i !== self.cursor) self.setCursor(P.i);
    });
    scroll.addEventListener('pointerleave', () => {
      const svg = scroll.firstChild; if (svg) svg.querySelector('.cell-hov').setAttribute('visibility', 'hidden');
    });
    scroll.addEventListener('click', e => {
      const P = locate(e); if (!P) return;
      if (opts.edit && self.onCell && P.lane && P.lane !== 'PCLK') { self.onCell(P.lane, P.i, e); return; }
      if (self.onPick) { self.onPick(P.i); return; }
      if (self.locked && self.cursor === P.i) self.setCursor(P.i, false); else self.setCursor(P.i, true);
    });
    scroll.addEventListener('keydown', e => {
      if (!self.wave) return;
      if (e.key === 'ArrowRight' || e.key === 'ArrowLeft') {
        e.preventDefault();
        const d = e.key === 'ArrowRight' ? 1 : -1;
        self.setCursor(Math.max(0, self.cursor + d), true);
        self.ensureVisible();
      } else if (e.key === 'Enter' && self.onPick && self.cursor >= 0) {
        self.onPick(self.cursor);
      } else if (e.key === 'Escape') self.setCursor(self.cursor, false);
    });
    return self;
  }

  /* ================================================================
     9. Readout panel bound to a waveform
     ================================================================ */
  function Readout(host, ctl, ro) {
    ro = Object.assign({ values: true, explain: true, empty: 'Hover over the waveform, or tap a cycle to pin it. Arrow keys step cycle by cycle.' }, ro || {});
    function render() {
      const w = ctl.wave, i = ctl.cursor;
      if (!w || i < 0) { host.innerHTML = `<p class="ro-empty">${ro.empty}</p>`; return; }
      const c = w.cycles[i], ph = phaseOf(w, i);
      const vs = ctl.opts.showViol ? ctl.viol.filter(v => v.i === i) : [];
      let h = '<div class="ro-head">';
      if (ro.explain) h += `<span class="chip ph-${ph}">${PHLABEL[ph]}</span>`;
      h += `<span class="ro-edge">Cycle ${i} · sampled at T${i + 1}${ctl.locked ? ' · pinned' : ''}</span></div>`;
      if (ro.explain) h += `<p class="ro-exp">${explain(w, i)}</p>`;
      if (vs.length) h += '<ul class="ro-viol">' + vs.map(v => `<li class="${v.sev}"><b>${v.rule}</b> ${esc(v.msg)}</li>`).join('') + '</ul>';
      if (ro.values) h += '<dl class="ro-vals">' + w.lanes.filter(l => l !== 'PCLK').map(l => `<div><dt class="g-${SIG[l].grp}">${l}</dt><dd>${fmtLong(l, c[l])}</dd></div>`).join('') + '</dl>';
      host.innerHTML = h;
    }
    ctl.on(render); render();
    return { render };
  }

  /* ================================================================
     10. First waveform (in Basics)
     ================================================================ */
  function initHero() {
    const host = $('#hero-wave'); if (!host) return;
    const ctl = Wave(host, { cw: 46, compact: true });
    Readout($('#hero-ro'), ctl, { values: false, empty: 'Move across the waveform. Each column is one clock cycle; the text here explains it.' });
    ctl.set(generate({ ver: 3, txns: [{ write: 1, addr: 0x20, data: 0xDEADBEEF, wait: 1, gap: 0 }, { write: 0, addr: 0x24, data: 0x0000C0DE, gap: 2 }] }));
    let hover = false;
    ctl.el.addEventListener('pointerenter', () => { hover = true; });
    ctl.el.addEventListener('pointerleave', () => { hover = false; });
    if (reduceMotion) { ctl.setCursor(2); return; }
    let i = 0;
    setInterval(() => {
      if (hover || ctl.locked || document.hidden) return;
      i = (i + 1) % ctl.wave.cycles.length;
      ctl.setCursor(i);
    }, 1400);
    ctl.setCursor(0);
  }

  /* ================================================================
     11. Signals table filter
     ================================================================ */
  function initSignals() {
    const seg = $('#sig-filter'); if (!seg) return;
    const apply = v => {
      $$('button', seg).forEach(b => b.setAttribute('aria-pressed', String(+b.dataset.ver === v)));
      $$('#sig-table tbody tr').forEach(tr => {
        const tv = +tr.dataset.v;
        tr.classList.toggle('na', tv > v);
        tr.classList.toggle('new', tv === v && v > 2);
      });
      const n = $$('#sig-table tbody tr').filter(tr => +tr.dataset.v <= v).length;
      $('#sig-count').textContent = `${n} signal${n === 1 ? '' : 's'} in APB${v}` + (v > 2 ? ' · highlighted rows are new in this version' : '');
    };
    seg.addEventListener('click', e => { const b = e.target.closest('button'); if (b) apply(+b.dataset.ver); });
    apply(3);
  }

  /* ================================================================
     12. State machine simulator
     ================================================================ */
  function initFSM() {
    const svg = $('#fsm-svg'); if (!svg) return;
    const ctl = Wave($('#fsm-wave'), { cw: 46, compact: true });
    const readyBox = $('#fsm-ready');
    const ARCWHY = {
      'idle-idle': 'no transfer is pending',
      'idle-setup': 'a transfer is requested',
      'setup-access': 'SETUP always lasts one cycle',
      'access-access': 'PREADY is low: wait state',
      'access-idle': 'PREADY is high and nothing is queued',
      'access-setup': 'PREADY is high and another transfer is queued'
    };
    const DESC = {
      IDLE: 'IDLE. No transfer. PSEL and PENABLE are low.',
      SETUP: 'SETUP. PSEL is high, PENABLE is low, address and control are on the bus.',
      ACCESS: 'ACCESS. PSEL and PENABLE are high. The completer decides with PREADY whether this is the last cycle.'
    };
    let state, queue, cur, hist, seq, last, log, timer = null;

    function reset() {
      state = 'IDLE'; queue = []; cur = null; hist = []; seq = 0; log = [];
      last = { PADDR: 'x', PWRITE: 'x', PWDATA: 'x' };
      stopAuto(); draw();
    }
    function cycleNow() {
      const ready = readyBox.checked ? 1 : 0;
      const o = Object.assign({ PSEL: 0, PENABLE: 0, PREADY: 0, PRDATA: 'x', PSLVERR: 0, PRESETn: 1 }, last);
      if (state === 'SETUP') o.PSEL = 1;
      if (state === 'ACCESS') { o.PSEL = 1; o.PENABLE = 1; o.PREADY = ready; if (ready && !cur.write) o.PRDATA = cur.data; }
      return o;
    }
    function next() {
      const ready = readyBox.checked;
      if (state === 'IDLE') return queue.length ? ['SETUP', 'idle-setup'] : ['IDLE', 'idle-idle'];
      if (state === 'SETUP') return ['ACCESS', 'setup-access'];
      if (!ready) return ['ACCESS', 'access-access'];
      return queue.length ? ['SETUP', 'access-setup'] : ['IDLE', 'access-idle'];
    }
    function clock() {
      hist.push(cycleNow());
      const [ns, arc] = next();
      log.unshift(`T${hist.length}: ${state} → ${ns}  ·  ${ARCWHY[arc]}`);
      log = log.slice(0, 7);
      if (ns === 'SETUP') {
        cur = queue.shift();
        last = { PADDR: cur.addr, PWRITE: cur.write, PWDATA: cur.write ? cur.data : last.PWDATA };
      }
      if (ns === 'IDLE') cur = null;
      state = ns; draw();
    }
    function draw() {
      $$('.fsm-state', svg).forEach(g => g.classList.toggle('on', g.dataset.state === state));
      const [ns, arc] = next();
      $$('.fsm-arc', svg).forEach(a => a.classList.toggle('next', a.dataset.arc === arc));
      $('#fsm-now').innerHTML = `<p><span class="chip ph-${state}">${state}</span> ${DESC[state]}</p><p class="fsm-next">At the next rising edge: <b>${state} → ${ns}</b>, because ${ARCWHY[arc]}.</p>`;
      $('#fsm-queue').innerHTML = queue.length
        ? queue.map(t => `<span class="qchip ${t.write ? 'w' : 'r'}">${t.write ? 'W' : 'R'} 0x${hexs(t.addr)}</span>`).join('')
        : '<span class="muted">empty</span>';
      $('#fsm-log').innerHTML = log.length ? log.map(l => `<li>${esc(l)}</li>`).join('') : '<li class="muted">Press “Clock edge” to advance one cycle.</li>';
      const w = { ver: 3, sels: ['PSEL'], lanes: ['PCLK', 'PSEL', 'PENABLE', 'PADDR', 'PWRITE', 'PWDATA', 'PREADY', 'PRDATA'], cycles: hist.concat([cycleNow()]) };
      ctl.set(w);
      ctl.setCursor(w.cycles.length - 1, true);
      ctl.scrollEnd();
    }
    function queueTxn(write) {
      const addr = 0x10 + 4 * (seq % 12);
      queue.push({ write, addr, data: write ? (0x1000 + seq) >>> 0 : (0xC0DE0000 + seq) >>> 0 });
      seq++; draw();
    }
    function stopAuto() { if (timer) clearInterval(timer); timer = null; const b = $('#fsm-auto'); if (b) { b.textContent = 'Run'; b.setAttribute('aria-pressed', 'false'); } }
    $('#fsm-qw').addEventListener('click', () => queueTxn(1));
    $('#fsm-qr').addEventListener('click', () => queueTxn(0));
    $('#fsm-clk').addEventListener('click', clock);
    $('#fsm-reset').addEventListener('click', reset);
    readyBox.addEventListener('change', draw);
    $('#fsm-auto').addEventListener('click', e => {
      if (timer) { stopAuto(); return; }
      timer = setInterval(clock, 950);
      e.currentTarget.textContent = 'Pause';
      e.currentTarget.setAttribute('aria-pressed', 'true');
    });
    reset();
    queueTxn(1); queueTxn(0);
  }

  /* ================================================================
     13. Small helpers shared by the lab
     ================================================================ */
  function codeBox(title, code) {
    return `<figure class="code mini"><figcaption><span>${esc(title)}</span></figcaption><pre><code>${hlSV(code)}</code></pre></figure>`;
  }
  function copyText(text, btn, sel) {
    const label = btn ? btn.textContent : '';
    const done = t => { if (!btn) return; btn.textContent = t; setTimeout(() => { btn.textContent = label; }, 1800); };
    const fallback = () => {
      if (sel && window.getSelection) { const r = document.createRange(); r.selectNodeContents(sel); const s = window.getSelection(); s.removeAllRanges(); s.addRange(r); done('Selected, press Ctrl+C'); }
      else done('Copy blocked here');
    };
    try {
      if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(text).then(() => done('Copied'), fallback);
      else fallback();
    } catch (e) { fallback(); }
  }
  // Public link to a part of the page: the configured site address, or the current
  // address when the page is self-hosted. Returns '' inside the claude.ai viewer.
  function shareUrl(key) {
    const main = $('main'), base = (main && main.dataset.siteUrl) || '';
    if (base) return base.replace(/#.*$/, '') + '#' + key;
    if (/^https?:$/.test(location.protocol) && !/claude/i.test(location.hostname)) return location.href.split('#')[0] + '#' + key;
    return '';
  }
  function opText(a) {
    if (a.op === 'always') return `No antecedent: <code>${esc(a.cons)}</code> is checked at every clock.`;
    if (a.op === '##') return `When <code>${esc(a.ante)}</code>, then <code>${esc(a.cons)}</code>. The window starts one clock after SETUP.`;
    return `When <code>${esc(a.ante)}</code> ${a.op === '|=>' ? '<b>|=&gt;</b> one clock later' : '<b>|-&gt;</b> in the same clock'} <code>${esc(a.cons)}</code> must hold.`;
  }
  function whyText(R) {
    const a = R.a, f = R.fails[0];
    if (!f) return '';
    if (a.op === '|=>') return `At <b>T${f.from + 1}</b> the antecedent <code>${esc(a.ante)}</code> is true (blue dot). <code>|=&gt;</code> checks the consequent one clock later, at <b>T${f.i + 1}</b>, and <code>${esc(a.cons)}</code> is false there (red cross). ${esc(f.msg)}`;
    if (a.op === '|->') return `At <b>T${f.i + 1}</b> the antecedent <code>${esc(a.ante)}</code> is true, and <code>|-&gt;</code> checks <code>${esc(a.cons)}</code> in the same clock. It is false. ${esc(f.msg)}`;
    if (a.op === '##') return `SETUP at <b>T${f.from + 1}</b> starts the attempt. No completion arrives within ${MAX_WAIT + 1} clocks, so the warning fires at <b>T${f.i + 1}</b>. ${esc(f.msg)}`;
    return `This property has no antecedent, so it is checked at every clock. At <b>T${f.i + 1}</b>: ${esc(f.msg)}`;
  }

  /* ================================================================
     14. Waveform lab: choose a scenario, then apply things to the
     waveform from one bar right above it. A result panel right under
     the waveform explains what is applied and what to look at.
     ================================================================ */
  const ASIG = {
    a_reset_idle: ['PRESETn', 'SEL', 'PENABLE'], a_no_x_sel: ['SEL', 'PENABLE'], a_psel_onehot: ['SEL'],
    a_en_needs_sel: ['SEL', 'PENABLE'], a_setup_to_access: ['SEL', 'PENABLE'], a_rose_en_after_setup: ['SEL', 'PENABLE'],
    a_wait_hold: ['SEL', 'PENABLE', 'PREADY'], a_stable_ctrl: ['PADDR', 'PWRITE', 'PPROT'], a_stable_wdata: ['PWDATA', 'PSTRB'],
    a_en_drop: ['PENABLE', 'PREADY'], a_strb_read: ['PWRITE', 'PSTRB'], a_no_x_ctrl: ['PADDR', 'PWRITE', 'PPROT'],
    a_no_x_wdata: ['PWDATA', 'PSTRB'], a_no_x_ready: ['PREADY'], a_no_x_err: ['PSLVERR'], a_no_x_rdata: ['PRDATA'],
    a_err_only_on_done: ['PSLVERR', 'PREADY'], a_max_wait: ['PREADY'], a_wake_during_xfer: ['PWAKEUP', 'SEL']
  };
  const CSHORT = {
    c_strb_read: 'reads get byte strobes', c_strb_write: 'strobes go uniform', c_wait: 'very long stalls', c_err: 'errors everywhere',
    c_aligned: 'unaligned addresses', c_in_range: 'addresses outside the map', c_idle: 'random gaps'
  };
  const CWANT = {
    c_strb_read: it => !it.dir && it.strb, c_strb_write: it => it.dir && it.strb !== 15, c_wait: it => it.wait > MAX_WAIT,
    c_err: it => it.err, c_aligned: it => it.addr & 3, c_in_range: it => it.unmapped, c_idle: it => it.idle > 3
  };
  function diffCells(a, b) {
    if (!a || !b) return [];
    const lanes = b.lanes.filter(l => l !== 'PCLK'), out = [], eq = (x, y) => String(x) === String(y);
    if (a.cycles.length === b.cycles.length) {
      b.cycles.forEach((c, i) => lanes.forEach(l => { if (!eq(c[l], a.cycles[i][l])) out.push({ lane: l, i }); }));
      return out;
    }
    const n = Math.min(a.cycles.length, b.cycles.length);
    let k = 0;
    while (k < n && lanes.every(l => eq(a.cycles[k][l], b.cycles[k][l]))) k++;
    if (k < b.cycles.length) lanes.forEach(l => out.push({ lane: l, i: k }));
    return out;
  }

  function initLab() {
    const root = $('#lab'); if (!root) return null;
    const ctl = Wave($('#lab-wave'), { cw: 54, markBand: true });
    Readout($('#lab-readout'), ctl);
    const verSel = $('#lab-ver'), body = $('#lab-txns'), stage = $('#lab-stage');
    const pop = $('#lab-pop'), badge = $('#lab-badge');
    let cfg, scenario = null, lastScenario = 'apb2-write', src = { kind: 'scenario' }, ref = null;
    let mode = 'build', results = [], applied = null, attK = 0, bug = null, playT = null;
    const bd = { a: 'setup', op: '|=>', c: 'access', R: null };
    const found = new Set(store.get('bugs', []));
    const consOn = Object.fromEntries(CONSTRAINTS.map(c => [c.id, true]));
    let cov = newCov(), runsDone = 0, lastRun = null;
    const hidden = () => !!(bug && !bug.revealed);
    const rank = r => (r.fails.length ? (r.a.sev === 'error' ? 0 : 1) : r.att.length ? 2 : 3);
    const CLS = ['fail', 'warn', 'pass', 'vac'];
    const ST = ['FAILS', 'WARNS', 'PASSES', 'NOT TRIGGERED'];
    const toWorkbench = () => scrollToId('step2');

    /* ----- results, including "my assertion" from the builder ----- */
    function mine() {
      const A = COND[bd.a], K = COND[bd.c];
      return { name: 'a_my_check', tag: 'Yours', sev: 'error', ver: 2, op: bd.op, ante: A.txt, cons: K.txt,
        plain: `When ${A.txt}, ${bd.op === '|=>' ? 'one clock later' : 'in the same clock'} ${K.txt}.`, sva: customSVA(bd.a, bd.op, bd.c) };
    }
    function resultOf(name) {
      if (name === '__mine__') { const r = evalCustom(ctl.wave, bd.a, bd.op, bd.c); return { a: mine(), att: r.att, fails: r.fails }; }
      return results.find(r => r.a.name === name);
    }
    function attempts(R) { return R.a.op === 'always' ? R.fails.map(f => f.from) : R.att; }
    function firstFailK(name) {
      const R = name && ctl.wave && resultOf(name); if (!R || !R.fails.length) return 0;
      const k = attempts(R).indexOf(R.fails[0].from); return k < 0 ? 0 : k;
    }
    function completion(i) { for (let j = i + 1; j < ctl.wave.cycles.length; j++) if (phaseOf(ctl.wave, j) === 'ACCESS') return j; return i; }
    function attemptInfo() {
      const R = applied && resultOf(applied); if (!R) return null;
      const list = attempts(R); if (!list.length) return null;
      const k = ((attK % list.length) + list.length) % list.length, i = list[k];
      const f = R.fails.find(x => x.from === i);
      const j = f ? f.i : R.a.op === '|=>' ? i + 1 : R.a.op === '##' ? completion(i) : i;
      return { R, k, n: list.length, i, j, f };
    }

    // Bring the interesting part of the waveform into view: the current check, else the first changed cell
    function focusFirst() {
      const A = !hidden() && attemptInfo();
      let i = A ? A.j : -1;
      if (i < 0 && ctl.focus && ctl.focus.cells && ctl.focus.cells.length) i = Math.min.apply(null, ctl.focus.cells.map(c => c.i));
      if (i >= 0) { ctl.setCursor(i, true); ctl.ensureVisible(); }
    }
    /* ----- draw everything that is applied ----- */
    function show(w, keep) {
      ctl.opts.showViol = !hidden();
      ctl.set(w, keep);
      results = evalAll(ctl.wave);
      if (applied && applied !== '__mine__' && !results.some(r => r.a.name === applied)) applied = null;
      attK = firstFailK(applied);
      refresh();
    }
    function refresh() {
      ctl.setShowViol(!hidden());
      paint(); status(); renderBar(); renderResult(); renderEditFails(); renderExport();
      if (mode === 'build') renderBuild();
    }
    function paint() {
      const w = ctl.wave;
      let lanes = [];
      if (applied && !hidden() && ASIG[applied]) lanes = ASIG[applied].flatMap(s => (s === 'SEL' ? w.sels : [s])).filter(l => w.lanes.includes(l));
      ctl.focus = { lanes, cells: diffCells(ref, w), kind: src.kind };
      let m = null;
      const R = !hidden() && applied && resultOf(applied);
      if (R) {
        const A = attemptInfo();
        m = { trig: R.att, fail: R.fails.map(f => f.i), links: R.fails.filter(f => f.from !== f.i).map(f => [f.from, f.i]), cur: A ? (A.i === A.j ? [A.i] : [A.i, A.j]) : null };
      }
      ctl.setMarks(m);
    }
    function status() {
      const st = $('#lab-status');
      if (hidden()) { st.className = 'lab-status info'; st.textContent = 'Bug inserted · assertions hidden until you guess'; return; }
      const fe = results.filter(r => r.fails.length && r.a.sev === 'error').length;
      const fw = results.filter(r => r.fails.length && r.a.sev === 'warn').length;
      st.className = 'lab-status ' + (fe ? 'bad' : fw ? 'warn' : 'ok');
      st.textContent = fe ? `${fe} assertion${fe > 1 ? 's fail' : ' fails'} on this waveform` + (fw ? ` · ${fw} warning${fw > 1 ? 's' : ''}` : '')
        : fw ? `Legal · ${fw} warning${fw > 1 ? 's' : ''}` : `All ${results.length} assertions pass`;
    }
    function setNow(label) { $('#lab-now').textContent = label; }

    /* ----- the apply bar ----- */
    const AGROUPS = [['The five rules', ['Rule 1', 'Rule 2', 'Rule 3', 'Rule 4', 'Rule 5']], ['No X allowed', ['X-check']], ['More checks', ['Reset', 'Decoder', 'APB4', 'APB5', 'Policy']]];
    const SYM = ['✕', '!', '✓', '○'];
    function consKey() {
      const off = CONSTRAINTS.filter(c => c.ver <= +verSel.value && !consOn[c.id]);
      return off.length === 0 ? 'all' : off.length === 1 ? off[0].id : 'custom';
    }
    function renderBar() {
      const sa = $('#ab-assert'), sb = $('#ab-bug'), sc = $('#ab-cons');
      if (hidden()) {
        sa.innerHTML = '<option value="">Guess first: answer under the waveform</option>'; sa.disabled = true;
      } else {
        sa.disabled = false;
        sa.innerHTML = '<option value="">None applied</option>' + AGROUPS.map(([g, tags]) => `<optgroup label="${g}">${ASSERTS.filter(a => tags.includes(a.tag)).map(a => {
          const R = results.find(r => r.a.name === a.name);
          return R ? `<option value="${a.name}">${SYM[rank(R)]} ${a.name}</option>` : `<option value="${a.name}" disabled>– ${a.name} (APB${a.ver}+)</option>`;
        }).join('')}</optgroup>`).join('') + `<optgroup label="Yours"><option value="__mine__">${(() => { const r = evalCustom(ctl.wave, bd.a, bd.op, bd.c); return r.fails.length ? '✕' : r.att.length ? '✓' : '○'; })()} My assertion (Build your own)</option></optgroup>`;
        sa.value = applied || '';
      }
      sb.innerHTML = '<option value="">No bug</option>' + ['Requester', 'Completer', 'Testbench'].map(g => `<optgroup label="${g} bugs">${BUGS.filter(b => b.who === g).map(b => `<option value="${b.id}">${found.has(b.id) ? '✓ ' : ''}${esc(b.title)}</option>`).join('')}</optgroup>`).join('');
      sb.value = src.kind === 'bug' ? src.id : '';
      const ver = +verSel.value;
      sc.innerHTML = '<option value="none">Off · showing a fixed waveform</option><option value="all">On · all constraints applied</option><optgroup label="Remove one constraint">' +
        CONSTRAINTS.map(c => `<option value="${c.id}">Without ${c.id} · ${CSHORT[c.id]}${c.ver > ver ? ` (switches to APB${c.ver})` : ''}</option>`).join('') + '</optgroup>' +
        (src.kind === 'random' && consKey() === 'custom' ? '<option value="custom">Custom set (from Go deeper)</option>' : '');
      sc.value = src.kind === 'random' ? consKey() : 'none';
      $('#ab-reseed').hidden = src.kind !== 'random';
      $$('.ab-f').forEach(f => f.classList.toggle('on', !!f.querySelector('select').value && !['none', ''].includes(f.querySelector('select').value)));
    }
    $('#ab-assert').addEventListener('change', e => { const v = e.target.value; if (!v) { applied = null; refresh(); } else applyAssert(v, true); });
    $('#ab-bug').addEventListener('change', e => { const v = e.target.value; if (v) insertBug(v); else backToScenario(); });
    $('#ab-cons').addEventListener('change', e => {
      const v = e.target.value;
      if (v === 'none') backToScenario();
      else if (v === 'all') { Object.keys(consOn).forEach(k => { consOn[k] = true; }); runRandom(newSeed(), { lead: '<b>All constraints applied.</b> Every item is legal, so the lab\'s assertions should all pass.' }); }
      else if (v !== 'custom') runExperiment(v);
    });
    $('#ab-reseed').addEventListener('click', () => {
      const k = consKey();
      if (k !== 'all' && k !== 'custom') runExperiment(k); else runRandom(newSeed());
    });
    $('#ab-reset').addEventListener('click', () => backToScenario(true));
    function backToScenario(resetAll) {
      Object.keys(consOn).forEach(k => { consOn[k] = true; });
      loadPreset(scenario || lastScenario);
      if (resetAll) { applied = presetById(scenario).focus; attK = 0; refresh(); }
      renderCons();
    }

    /* ----- the result panel under the waveform ----- */
    function attemptText(a, A) {
      const mark = A.f ? `<b class="badc">✕ fails.</b> ${esc(A.f.msg)}` : '<b class="okc">✓ holds.</b>';
      if (a.op === '|=>') return `At <b>T${A.i + 1}</b>, ${esc(a.ante)} is true. One clock later, at <b>T${A.j + 1}</b>, check that ${esc(a.cons)}: ${mark}`;
      if (a.op === '|->') return `At <b>T${A.i + 1}</b>, ${esc(a.ante)} is true. In the same clock, check that ${esc(a.cons)}: ${mark}`;
      if (a.op === '##') return A.f ? `SETUP at <b>T${A.i + 1}</b>. No completion by <b>T${A.j + 1}</b>: <b class="badc">✕ fails.</b> ${esc(A.f.msg)}`
        : `SETUP at <b>T${A.i + 1}</b>. The transfer completes at <b>T${A.j + 1}</b>, after ${A.j - A.i - 1} wait state${A.j - A.i - 1 === 1 ? '' : 's'}: <b class="okc">✓ within the limit.</b>`;
      return `At <b>T${A.j + 1}</b>: ${mark}`;
    }
    function sourceBlock() {
      const p = presetById(scenario);
      if (src.kind === 'bug' && bug) {
        return `<div class="rs-src is-bug"><span class="rs-tag">Bug inserted</span><p><b>${esc(bug.def.title)}.</b> ${bug.removed ? 'Removed again: this is the clean waveform.' : 'The red outlined cells are what the bug changed.'}${shareUrl('bug-' + bug.def.id) ? ` <button type="button" class="linkbtn share-link" data-share="bug-${bug.def.id}">Copy a link to this bug</button>` : ''}</p></div>`;
      }
      if (src.kind === 'random') {
        const k = consKey();
        const what = k === 'all' ? 'all constraints applied' : k === 'custom' ? 'a custom set of constraints' : `without <code>${k}</code>`;
        return `<div class="rs-src is-rnd"><span class="rs-tag">Random stimulus</span><p><b>Seed ${src.seed}</b>, ${what}.${ref ? ' The amber outlined cells are what that change did, compared with the same seed.' : ''} Press <b>New seed</b> for another run.</p>${src.lead ? `<p class="small">${src.lead}</p>` : ''}</div>`;
      }
      if (src.kind === 'edit') {
        return `<div class="rs-src is-edit"><span class="rs-tag">Edited by hand</span><p>${esc(src.label || 'The amber outlined cells are your edits.')} ${ref ? '<button type="button" class="linkbtn" data-rs="undo">Undo my edits</button>' : ''}</p></div>`;
      }
      if (src.kind === 'custom') return '<div class="rs-src"><span class="rs-tag">Your transfers</span><p>Built in the transfer table. Choose a scenario above to go back to a guided one.</p></div>';
      return p ? `<div class="rs-src"><span class="rs-tag">Scenario</span><p><b>${esc(p.short)}.</b> ${esc(p.tip)}${shareUrl('scenario-' + p.id) ? ` <button type="button" class="linkbtn share-link" data-share="scenario-${p.id}">Copy a link to this scenario</button>` : ''}</p></div>` : '';
    }
    function bugBlock() {
      if (!bug) return '';
      const d = bug.def;
      if (!bug.revealed) {
        return `<div class="rs-bug"><p class="rs-q"><b>Which assertion catches this bug?</b> Look at the waveform above, then pick one.</p>
          <div class="bc-opts">${bug.choices.map(n => `<button type="button" class="bc-opt" data-pick="${n}"><code>${n}</code><span>${esc(AMAP[n].plain)}</span></button>`).join('')}</div>
          <button type="button" class="linkbtn" data-pick="">Skip and show me the answer</button></div>`;
      }
      let h = '<div class="rs-bug">';
      if (bug.pick === '') h += '<p class="bc-verdict info"><b>Here is the answer.</b></p>';
      else if (bug.correct) h += `<p class="bc-verdict ok"><b>Correct.</b> <code>${bug.pick}</code> catches it. It is now applied, so you can see where it fails.</p>`;
      else h += `<p class="bc-verdict no"><b>Not this one.</b> <code>${bug.pick}</code> still passes: “${esc(AMAP[bug.pick].plain)}” The one that catches it, <code>${d.catches}</code>, is now applied.</p>`;
      const others = bug.allFails.filter(n => n !== d.catches);
      if (others.length) h += `<p class="small muted">Also failing: ${others.map(n => `<code>${n}</code>`).join(', ')}.</p>`;
      if (d.note) h += `<p class="small callout">${esc(d.note)}</p>`;
      h += `<details class="rs-more"><summary>Show the buggy code and the fix</summary><p>${esc(d.story)}</p>${codeBox('The buggy code', d.code)}<p><b>${d.constraint ? 'Fix it in the testbench' : 'The fix'}.</b> ${esc(d.fix)}</p>${codeBox(d.constraint ? 'Testbench fix' : 'Fixed code', d.fixCode)}</details>`;
      h += `<div class="bc-actions"><button type="button" class="btn" data-rs="toggle">${bug.removed ? 'Put the bug back' : 'Remove the bug'}</button><button type="button" class="btn primary" data-rs="next">Next bug →</button></div></div>`;
      return h;
    }
    function assertBlock() {
      if (hidden()) return '';
      if (!applied) return '<p class="rs-hint">Pick one in <b>Apply an assertion</b> above to see where it checks this waveform. The signals it looks at light up, blue dots mark each check, and a red cross marks a failure.</p>';
      const R = resultOf(applied); if (!R) return '';
      const a = R.a, k = rank(R), A = attemptInfo();
      const sug = scenario && src.kind === 'scenario' && presetById(scenario).focus === applied ? '<span class="sug">Suggested for this scenario</span>' : '';
      const look = applied !== '__mine__' && ASIG[applied] ? ASIG[applied].map(s => (s === 'SEL' ? ctl.wave.sels.join(', ') : s)).filter(s => ctl.wave.lanes.some(l => s.includes(l))).join(', ') : '';
      const [opSym, opSub] = { '|->': ['|->', 'same clock'], '|=>': ['|=>', 'next clock'], '##': [`##[1:${MAX_WAIT + 1}]`, 'within the window'], always: ['always', 'every clock'] }[a.op];
      let h = `<div class="rs-as ${CLS[k]}"><div class="rs-as-h"><span class="ap-st ${CLS[k]}">${ST[k]}</span><code class="ap-name">${a.name}</code><span class="as-tag">${a.tag}</span>${sug}</div>
        <p class="rs-plain">${esc(a.plain)}</p>`;
      if (look) h += `<p class="small rs-look">Look at the highlighted signals: <b>${esc(look)}</b>.</p>`;
      h += `<div class="ap-flow"><div class="ap-box"><span>When</span><code>${esc(a.op === 'always' ? 'every clock' : a.ante)}</code></div><div class="ap-arrow"><b>${esc(opSym)}</b><small>${opSub}</small></div><div class="ap-box"><span>Then</span><code>${esc(a.cons)}</code></div></div>`;
      if (k === 3) {
        const alt = applied !== '__mine__' && PRESETS.find(p => p.cfg.ver >= a.ver && (evalAll(generate(clone(p.cfg))).find(r => r.a.name === a.name) || { att: [] }).att.length);
        h += `<p><b>Not triggered here.</b> Nothing in this waveform makes “${esc(a.ante)}” true, so it checked nothing. That is a vacuous pass, and it proves nothing.</p>`;
        if (alt) h += `<div><button type="button" class="btn sm" data-scn="${alt.id}">Load “${esc(alt.short)}”, where it does check →</button></div>`;
      } else {
        h += `<p>${R.fails.length ? `<b>Fails ${R.fails.length}× on this waveform.</b>` : `<b>Checked ${a.op === 'always' ? 'at every clock' : R.att.length + '×'}, passed every time.</b>`}</p>`;
        if (A) h += `<div class="ap-step"><button type="button" class="btn sm" data-st="-1" aria-label="Previous check">◀</button><span>Check ${A.k + 1} of ${A.n}</span><button type="button" class="btn sm" data-st="1" aria-label="Next check">▶</button></div><p class="ap-att">${attemptText(a, A)}</p>`;
      }
      h += `<details class="rs-more"><summary>Show the SystemVerilog</summary>${codeBox('SystemVerilog', a.sva)}</details>`;
      const b = applied !== '__mine__' && !bug && BUGS.find(x => x.catches === applied);
      if (b) h += `<div class="ap-break"><span>See it catch a real bug:</span><button type="button" class="btn sm primary" data-ap-bug="${b.id}">Insert “${esc(b.title)}”</button></div>`;
      return h + '</div>';
    }
    function renderResult() {
      $('#lab-result').innerHTML = sourceBlock() + bugBlock() + assertBlock() +
        (mode === 'edit' ? '<p class="rs-edit-on">Edit mode is on: click any 1-bit signal on the waveform to flip it, or a bus to type a value.</p>' : '');
    }
    function applyAssert(name, jump) {
      applied = name; attK = firstFailK(name);
      paint(); renderBar(); renderResult();
      if (jump) { const A = attemptInfo(); if (A) { ctl.setCursor(A.j, true); ctl.ensureVisible(); } }
    }
    $('#lab-result').addEventListener('click', e => {
      const sh = e.target.closest('[data-share]'); if (sh) { copyText(shareUrl(sh.dataset.share), sh, null); return; }
      const st = e.target.closest('[data-st]');
      if (st) { attK += +st.dataset.st; paint(); renderResult(); const A = attemptInfo(); if (A) { ctl.setCursor(A.j, true); ctl.ensureVisible(); } return; }
      const sc = e.target.closest('[data-scn]'); if (sc) { const keep = applied; loadPreset(sc.dataset.scn); applyAssert(keep, true); return; }
      const bb = e.target.closest('[data-ap-bug]'); if (bb) { insertBug(bb.dataset.apBug); return; }
      const p = e.target.closest('[data-pick]');
      if (p && bug && !bug.revealed) {
        const n = p.dataset.pick;
        bug.pick = n;
        bug.correct = !!n && results.some(r => r.a.name === n && r.fails.length);
        bug.allFails = results.filter(r => r.fails.length).map(r => r.a.name);
        bug.revealed = true;
        if (bug.correct) { found.add(bug.def.id); store.set('bugs', Array.from(found)); renderBugPick(); progress(); }
        applied = bug.def.catches; attK = firstFailK(applied);
        refresh();
        const A = attemptInfo(); if (A) { ctl.setCursor(A.j, true); ctl.ensureVisible(); }
        return;
      }
      const a = e.target.closest('[data-rs]'); if (!a) return;
      if (a.dataset.rs === 'undo' && ref) { const w = ref; ref = null; src = { kind: scenario ? 'scenario' : 'custom' }; setEdited(false); show(clone(w), true); return; }
      if (a.dataset.rs === 'next' && bug) {
        const k = BUGS.indexOf(bug.def), order = BUGS.slice(k + 1).concat(BUGS.slice(0, k + 1));
        insertBug((order.find(b => !found.has(b.id)) || order[0]).id); return;
      }
      if (a.dataset.rs === 'toggle' && bug) {
        bug.removed = !bug.removed;
        const d = bug.def;
        cfg = clone(bug.removed && d.clean ? d.clean : d.cfg); renderTable();
        ref = bug.removed ? null : generate(clone(d.clean || d.cfg));
        show(bug.removed ? generate(clone(d.clean || d.cfg)) : bugWave(d), true);
      }
    });

    /* ----- step 1: scenario chooser ----- */
    $('#scn').innerHTML = SGRP.map(g => `<div class="scn-g"><span class="lbl-sm">${esc(g)}</span><div class="scn-list">${PRESETS.filter(p => p.grp === g).map(p => `<button type="button" class="scn-b" data-p="${p.id}" aria-pressed="false"><b>${esc(p.short)}</b><small>${esc(p.learn)}</small></button>`).join('')}</div></div>`).join('');
    $('#scn').addEventListener('click', e => { const b = e.target.closest('[data-p]'); if (b) loadPreset(b.dataset.p); });
    function renderScenario() {
      $$('#scn .scn-b').forEach(b => b.setAttribute('aria-pressed', String(src.kind === 'scenario' && b.dataset.p === scenario)));
    }

    /* ----- go deeper tabs ----- */
    const MODES = ['build', 'cons', 'bug', 'edit'];
    function setMode(m) {
      mode = m;
      $$('#lab-modes [data-mode]').forEach(b => { const on = b.dataset.mode === m; b.setAttribute('aria-selected', String(on)); b.tabIndex = on ? 0 : -1; });
      MODES.forEach(x => { $('#m-' + x).hidden = x !== m; });
      ctl.setEdit(m === 'edit');
      closePop();
      if (m !== 'edit') badge.hidden = true;
      if (m === 'cons') { renderCons(); renderCov(); }
      refresh();
    }
    $('#lab-modes').addEventListener('click', e => { const b = e.target.closest('[data-mode]'); if (b) setMode(b.dataset.mode); });
    $('#lab-modes').addEventListener('keydown', e => {
      if (e.key !== 'ArrowRight' && e.key !== 'ArrowLeft') return;
      const tabs = $$('#lab-modes [data-mode]'), k = tabs.findIndex(t => t.dataset.mode === mode);
      const n = tabs[(k + (e.key === 'ArrowRight' ? 1 : tabs.length - 1)) % tabs.length];
      setMode(n.dataset.mode); n.focus();
    });

    /* ----- bugs ----- */
    const GRP = { Requester: 'Requester bugs · bridge or driver', Completer: 'Completer bugs · peripheral', Testbench: 'Stimulus and testbench bugs · fixed in the testbench' };
    function renderBugPick() {
      $('#bug-pick').innerHTML = Object.keys(GRP).map(g => `<div class="bp-grp"><span class="lbl-sm">${GRP[g]}</span><div class="bp-list">${BUGS.filter(b => b.who === g).map(b => `<button type="button" class="bp${found.has(b.id) ? ' found' : ''}" data-bug="${b.id}"><span>${esc(b.title)}</span><small>${b.tag}</small></button>`).join('')}</div></div>`).join('');
      $('#bug-count').textContent = `${found.size} of ${BUGS.length} caught`;
    }
    function insertBug(id, noScroll) {
      const def = BUGS.find(b => b.id === id); if (!def) return;
      stopPlay();
      cfg = clone(def.cfg); verSel.value = String(cfg.ver); renderTable();
      src = { kind: 'bug', id }; ref = generate(clone(def.clean || def.cfg));
      bug = { def, choices: shuffle([def.catches].concat(def.decoys)), revealed: false, removed: false, pick: null };
      applied = null; setEdited(false);
      renderScenario(); setNow(`Bug: ${def.title}`);
      show(bugWave(def));
      focusFirst();
      if (!noScroll) toWorkbench();
    }
    function clearBug() { bug = null; }
    $('#bug-pick').addEventListener('click', e => { const b = e.target.closest('[data-bug]'); if (b) insertBug(b.dataset.bug); });
    $('#bug-rand').addEventListener('click', () => {
      const open = BUGS.filter(b => !found.has(b.id)), pool = open.length ? open : BUGS;
      insertBug(pool[Math.floor(Math.random() * pool.length)].id);
    });

    /* ----- random stimulus and constraints ----- */
    const nItems = () => Math.max(1, Math.min(8, parseInt($('#rc-n').value, 10) || 4));
    const newSeed = () => { const s = 1 + Math.floor(Math.random() * 999999); $('#rc-seed').value = s; return s; };
    $('#rc-seed').value = 1 + Math.floor(Math.random() * 99999);
    function runRandom(s, o) {
      o = o || {};
      const ver = +verSel.value;
      const items = randomize(s, nItems(), consOn, ver);
      sampleCov(cov, items, ver); runsDone++;
      const prev = o.diffPrev && lastRun && lastRun.seed === s && lastRun.ver === ver && lastRun.items.length === items.length ? lastRun.items : null;
      ref = o.refWave || (prev ? generate(itemsToCfg(prev, ver)) : null);
      lastRun = { seed: s, ver, items };
      $('#rc-seed').value = s;
      clearBug(); stopPlay();
      cfg = itemsToCfg(items, ver); renderTable();
      src = { kind: 'random', seed: s, lead: o.lead || '' };
      renderScenario(); setNow(`Random stimulus · seed ${s}`);
      if (applied === null && consKey() !== 'all') { const k = consKey(); if (k === 'c_strb_read') applied = 'a_strb_read'; else if (k === 'c_wait') applied = 'a_max_wait'; }
      show(generate(cfg)); setEdited(false);
      focusFirst();
      renderRandomResults(items, ver, prev);
      if (o.scroll) toWorkbench();
    }
    function runExperiment(id) {
      const c = CONSTRAINTS.find(x => x.id === id);
      if (+verSel.value < c.ver) { verSel.value = String(c.ver); cfg.ver = c.ver; cov = newCov(); runsDone = 0; lastRun = null; }
      Object.keys(consOn).forEach(k => { consOn[k] = k !== id; });
      const ver = +verSel.value, allOn = Object.fromEntries(CONSTRAINTS.map(x => [x.id, true]));
      let s = newSeed();
      for (let t = 0; t < 500; t++) { if (randomize(s, nItems(), consOn, ver).some(CWANT[id])) break; s = s % 999999 + 1; }
      const legal = generate(itemsToCfg(randomize(s, nItems(), allOn, ver), ver));
      if (id === 'c_strb_read') applied = 'a_strb_read';
      else if (id === 'c_wait') applied = 'a_max_wait';
      else if (id === 'c_err' || id === 'c_in_range') applied = 'a_err_only_on_done';
      else applied = null;
      runRandom(s, { refWave: legal, lead: `<code>${id}</code> removed: ${esc(c.ifOff)}` });
      renderCons();
    }
    function renderCons() {
      const ver = +verSel.value;
      $('#rc-list').innerHTML = CONSTRAINTS.map(c => {
        const na = c.ver > ver, on = consOn[c.id];
        return `<li class="cc-card ${na ? 'na' : on ? 'on' : 'off'}">
          <div class="cc-top"><label class="switch" for="rc-${c.id}"><input type="checkbox" id="rc-${c.id}" data-c="${c.id}"${on ? ' checked' : ''}${na ? ' disabled' : ''}><code>${c.id}</code></label><span class="cc-state">${na ? `needs APB${c.ver}` : on ? 'applied' : 'removed'}</span></div>
          <p class="cc-plain">${esc(c.plain)}</p>
          <code class="rc-code">${esc(c.code)}</code>
          ${na ? '' : `<p class="cc-if"><b>${on ? 'If you remove it' : 'Removed'}:</b> ${esc(c.ifOff)}</p>`}
        </li>`;
      }).join('');
    }
    $('#rc-list').addEventListener('change', e => {
      const c = e.target.dataset.c; if (!c) return;
      consOn[c] = e.target.checked; renderCons();
      runRandom(lastRun ? lastRun.seed : newSeed(), { diffPrev: true, scroll: true });
    });
    const FIELDS_NOTE = (items, ver) => {
      const notes = [];
      const rdStrb = ver >= 4 ? items.filter(it => !it.dir && it.strb).length : 0;
      const longW = items.filter(it => it.wait > MAX_WAIT).length;
      const unal = items.filter(it => it.addr & 3).length;
      const unm = items.filter(it => it.unmapped).length;
      if (rdStrb) notes.push(['bad', `${rdStrb} read${rdStrb > 1 ? 's' : ''} went out with strobes, so <code>a_strb_read</code> fails.`]);
      if (longW) notes.push(['warn', `A transfer waited ${Math.max.apply(null, items.map(it => it.wait))} cycles, so <code>a_max_wait</code> warns.`]);
      if (unal) notes.push(['warn', `${unal} unaligned address${unal > 1 ? 'es' : ''}. No assertion fires: APB allows any address.`]);
      if (unm) notes.push(['warn', `${unm} address${unm > 1 ? 'es fall' : ' falls'} outside the 4 KB map${ver >= 3 ? ', answered with PSLVERR' : ''}.`]);
      if (!notes.length) notes.push(['ok', 'Every item is legal.']);
      return notes;
    };
    function renderRandomResults(items, ver, prev) {
      const cols = ['#', 'dir', 'addr', 'data'].concat(ver >= 4 ? ['strb', 'prot'] : [], ver >= 3 ? ['wait', 'err'] : [], ['idle']);
      $('#rc-res-head').innerHTML = '<tr>' + cols.map(c => `<th scope="col">${c}</th>`).join('') + '</tr>';
      $('#rc-res').innerHTML = items.map((it, k) => {
        const ch = f => (prev && prev[k][f] !== it[f] && !(f === 'idle' && k === 0) ? ' chg' : '');
        let r = `<tr><td>${k + 1}</td><td class="${ch('dir')}">${it.dir ? 'WRITE' : 'READ'}</td>`;
        r += `<td class="${it.unmapped || (it.addr & 3) ? 'amb' : ''}${ch('addr')}">0x${hexs(it.addr).padStart(3, '0')}</td><td class="${ch('data')}">0x${hexs(it.data)}</td>`;
        if (ver >= 4) r += `<td class="${!it.dir && it.strb ? 'bad' : ''}${ch('strb')}">${it.strb.toString(2).padStart(4, '0')}</td><td class="${ch('prot')}">${it.prot.toString(2).padStart(3, '0')}</td>`;
        if (ver >= 3) r += `<td class="${it.wait > MAX_WAIT ? 'bad' : ''}${ch('wait')}">${it.wait}</td><td class="${it.unmapped ? 'amb' : ''}${ch('err')}">${it.err}</td>`;
        return r + `<td class="${ch('idle')}">${k ? it.idle : '–'}</td></tr>`;
      }).join('');
      $('#rc-res-wrap').hidden = false;
      $('#rc-notes').innerHTML = FIELDS_NOTE(items, ver).map(([c, t]) => `<p class="${c}">${t}</p>`).join('');
      renderCov();
    }
    function renderCov() {
      const ver = +verSel.value, cps = COVER.filter(c => c.ver <= ver);
      let hit = 0, tot = 0; const miss = [];
      $('#cov-grid').innerHTML = cps.map(c => {
        const counts = cov[c.cp], h = counts.filter(x => x > 0).length;
        hit += h; tot += counts.length;
        c.bins.forEach((b, k) => { if (!counts[k]) miss.push(`${c.cp}.${b}`); });
        return `<div class="cv-row"><code>${c.cp}</code><div class="cv-bins">${c.bins.map((b, k) => `<span class="cv-bin${counts[k] ? ' hit' : ''}" title="${esc(b)}: ${counts[k]} hit${counts[k] === 1 ? '' : 's'}"><b>${esc(b)}</b><small>${counts[k]}</small></span>`).join('')}</div><span class="cv-pct">${Math.round(h / counts.length * 100)}%</span></div>`;
      }).join('');
      const pct = tot ? Math.round(hit / tot * 100) : 0;
      $('#cov-total').textContent = `${pct}% · ${runsDone} run${runsDone === 1 ? '' : 's'}`;
      $('#cov-bar i').style.width = pct + '%';
      $('#cov-miss').innerHTML = !runsDone ? 'Every random run, from the bar above the waveform or from here, fills these bins.'
        : miss.length ? `Still missing: ${miss.slice(0, 6).map(m => `<code>${esc(m)}</code>`).join(' ')}${miss.length > 6 ? ` and ${miss.length - 6} more` : ''}.`
        : `<b>100% coverage</b> in ${runsDone} runs.`;
    }
    $('#rc-go').addEventListener('click', () => runRandom(newSeed(), { scroll: true }));
    $('#rc-again').addEventListener('click', () => runRandom(Math.max(1, parseInt($('#rc-seed').value, 10) || 1), { scroll: true }));
    $('#rc-20').addEventListener('click', () => {
      for (let k = 0; k < 19; k++) { const ver = +verSel.value; sampleCov(cov, randomize(1 + Math.floor(Math.random() * 999999), nItems(), consOn, ver), ver); runsDone++; }
      runRandom(newSeed());
    });
    $('#cov-reset').addEventListener('click', () => { cov = newCov(); runsDone = 0; renderCov(); });

    /* ----- edit by hand ----- */
    function renderEditFails() {
      const host = $('#edit-fails'); if (!host) return;
      const F = results.filter(r => r.fails.length);
      host.innerHTML = F.length ? F.map(r => `<li class="${r.a.sev}"><code>${r.a.name}</code> fails at T${r.fails[0].i + 1}. ${esc(r.a.plain)} <button type="button" class="linkbtn" data-goa="${r.a.name}">Apply it to the waveform ↑</button></li>`).join('')
        : '<li class="ok">Every assertion passes. Change a signal to break one.</li>';
    }
    $('#edit-fails').addEventListener('click', e => { const b = e.target.closest('[data-goa]'); if (b) { applyAssert(b.dataset.goa, true); toWorkbench(); } });

    /* ----- build your own assertion ----- */
    const opts = keys => keys.map(k => `<option value="${k}">${esc(COND[k].txt)}</option>`).join('');
    $('#bd-a').innerHTML = opts(B_ANTE); $('#bd-c').innerHTML = opts(B_CONS);
    $('#bd-a').value = bd.a; $('#bd-op').value = bd.op; $('#bd-c').value = bd.c;
    ['#bd-a', '#bd-op', '#bd-c'].forEach(s => $(s).addEventListener('change', () => {
      bd.a = $('#bd-a').value; bd.op = $('#bd-op').value; bd.c = $('#bd-c').value;
      if (!hidden()) applyAssert('__mine__', true);
      renderBuild();
    }));
    let LEGAL = null, BUGW = null;
    function bdScore() {
      LEGAL = LEGAL || PRESETS.map(p => ({ id: p.id, label: p.short, w: generate(clone(p.cfg)) }));
      BUGW = BUGW || BUGS.map(b => ({ id: b.id, label: b.title, w: bugWave(b) }));
      const lf = LEGAL.filter(x => evalCustom(x.w, bd.a, bd.op, bd.c).fails.length);
      const latt = LEGAL.reduce((s, x) => s + evalCustom(x.w, bd.a, bd.op, bd.c).att.length, 0);
      const caught = BUGW.filter(x => evalCustom(x.w, bd.a, bd.op, bd.c).fails.length);
      return { lf, latt, caught };
    }
    const bdSolved = new Set(store.get('build', []));
    function renderBuild() {
      if (!$('#bd-res') || !ctl.wave) return;
      const A = COND[bd.a], K = COND[bd.c], R = evalCustom(ctl.wave, bd.a, bd.op, bd.c);
      $('#bd-code').innerHTML = hlSV(customSVA(bd.a, bd.op, bd.c));
      $('#bd-say').textContent = `When ${A.txt}, ${bd.op === '|=>' ? 'one clock later' : 'in the same clock'} check that ${K.txt}.`;
      const lib = B_LIB[bd.a + bd.op + bd.c];
      let h = `<p><b>${!R.att.length ? 'Not triggered' : R.fails.length ? `Fails ${R.fails.length}×` : `Passes, ${R.att.length} check${R.att.length > 1 ? 's' : ''}`}</b> on the waveform above.</p>`;
      h += applied === '__mine__' ? '<p class="small">It is applied there as <b>My assertion</b>, with every check marked. <button type="button" class="linkbtn" data-bd-up>Show me ↑</button></p>'
        : '<p class="small"><button type="button" class="linkbtn" data-bd-apply>Apply it to the waveform ↑</button></p>';
      if (lib) h += `<p class="bd-lib">You rebuilt <code>${lib}</code>, one of the lab's own checks.</p>`;
      if ((K.ver || 2) > ctl.wave.ver || (A.ver || 2) > ctl.wave.ver) h += `<p class="small muted">This uses a signal from APB${Math.max(K.ver || 2, A.ver || 2)}. On older versions it passes without checking.</p>`;
      const res = $('#bd-res'); res.className = 'ap-res ' + (!R.att.length ? 'vac' : R.fails.length ? 'fail' : 'pass'); res.innerHTML = h;
      renderScore();
    }
    function renderScore() {
      const S = bdScore(), legalOk = LEGAL.length - S.lf.length;
      let v;
      if (S.lf.length) v = `<p class="bd-v bad"><b>Too strict.</b> It fails on ${S.lf.length} legal scenario${S.lf.length > 1 ? 's' : ''}. A real assertion must never fail on legal traffic. Click one to see why:</p>`;
      else if (!S.latt) v = '<p class="bd-v warn"><b>Never triggers.</b> No legal scenario makes the “When” part true, so this assertion checks nothing anywhere.</p>';
      else if (!S.caught.length) v = '<p class="bd-v warn"><b>Safe but toothless.</b> It passes on every legal scenario but catches none of the 14 bugs. Try a stricter “Then”.</p>';
      else v = `<p class="bd-v ok"><b>Good assertion.</b> It passes on every legal scenario and catches ${S.caught.length} of the 14 bugs.</p>`;
      $('#bd-all').innerHTML = `<div class="bd-score"><div class="${S.lf.length ? 'bad' : 'ok'}"><b>${legalOk}/${LEGAL.length}</b><span>legal scenarios pass</span></div><div class="${S.caught.length ? 'ok' : 'warn'}"><b>${S.caught.length}/${BUGW.length}</b><span>bugs caught</span></div></div>${v}` +
        (S.lf.length ? `<div class="chipline">${S.lf.map(x => `<button type="button" class="chip-b bad" data-bd-scn="${x.id}">${esc(x.label)}</button>`).join('')}</div>` : '') +
        (S.caught.length && !S.lf.length ? `<div class="chipline">${S.caught.map(x => `<button type="button" class="chip-b ok" data-bd-bug="${x.id}">${esc(x.label)}</button>`).join('')}</div>` : '');
      let changed = false;
      $('#bd-ch').innerHTML = B_CHALLENGES.map(ch => {
        const b = BUGS.find(x => x.id === ch.bug);
        const ok = !S.lf.length && S.caught.some(x => x.id === ch.bug);
        if (ok && !bdSolved.has(ch.bug)) { bdSolved.add(ch.bug); changed = true; }
        const done = bdSolved.has(ch.bug);
        return `<li class="${done ? 'done' : ''}${ok ? ' is-now' : ''}"><span class="bd-mark" aria-hidden="true">${done ? '✓' : '○'}</span><div><p>Catch <b>${esc(b.title)}</b> without failing any legal scenario.${ok ? ' <b class="okc">Solved with this assertion.</b>' : ''}</p>
          <div class="bd-ch-act"><button type="button" class="linkbtn" data-bd-bug="${b.id}">Show this bug on the waveform ↑</button><details><summary>Hint</summary><p>${esc(ch.hint)}</p></details></div></div></li>`;
      }).join('');
      $('#bd-ch-count').textContent = `${bdSolved.size} of ${B_CHALLENGES.length} solved`;
      if (changed) { store.set('build', Array.from(bdSolved)); progress(); }
    }
    function loadBugWave(id) {
      const def = BUGS.find(b => b.id === id); if (!def) return;
      stopPlay(); clearBug();
      cfg = clone(def.cfg); verSel.value = String(cfg.ver); renderTable();
      src = { kind: 'edit', label: `This is the waveform of the bug “${def.title}”, without the guessing game. The amber outlined cells are what the bug changed.` };
      ref = generate(clone(def.clean || def.cfg));
      renderScenario(); setNow(`Bug waveform: ${def.title}`);
      applied = '__mine__';
      show(bugWave(def));
      focusFirst();
      toWorkbench();
    }
    $('#m-build').addEventListener('click', e => {
      if (e.target.closest('[data-bd-up]')) { toWorkbench(); return; }
      if (e.target.closest('[data-bd-apply]')) { applyAssert('__mine__', true); renderBuild(); toWorkbench(); return; }
      const s = e.target.closest('[data-bd-scn]'); if (s) { loadPreset(s.dataset.bdScn); applyAssert('__mine__', true); toWorkbench(); return; }
      const b = e.target.closest('[data-bd-bug]'); if (b) loadBugWave(b.dataset.bdBug);
    });
    $('#bd-copy').addEventListener('click', e => copyText(customSVA(bd.a, bd.op, bd.c), e.currentTarget, $('#bd-code')));

    /* ----- run on a real simulator ----- */
    const svW = n => (n === 'PSTRB' ? 4 : n === 'PPROT' ? 3 : SIG[n] && SIG[n].w > 1 ? 32 : 1);
    function svVal(n, v) {
      const W = svW(n);
      if (isX(v)) return W === 1 ? "1'bx" : W === 32 ? "32'hxxxx_xxxx" : `${W}'b${'x'.repeat(W)}`;
      if (W === 1) return `1'b${v}`;
      if (W === 32) return `32'h${hexs(v).padStart(8, '0').replace(/(.{4})(.{4})/, '$1_$2')}`;
      return `${W}'b${v.toString(2).padStart(W, '0')}`;
    }
    function exportSV(withMine) {
      const w = ctl.wave, ver = w.ver, ns = w.sels.length, C = w.cycles;
      const fails = results.filter(r => r.fails.length).map(r => r.a.name);
      const L = [];
      L.push('// ------------------------------------------------------------------');
      L.push(`// PosEdge APB Lab export · ${$('#lab-now').textContent} · APB${ver}`);
      L.push('// The same waveform and the same assertions as the lab, for a real simulator.');
      L.push(`// Expected: ${fails.length ? fails.join(', ') + ' should fail.' : 'every assertion passes.'}${withMine ? ' a_my_check is your builder assertion.' : ''}`);
      L.push('//');
      L.push('// How to run it on EDA Playground (www.edaplayground.com):');
      L.push('//   1. Log in with a free account.');
      L.push('//   2. Paste this whole file into testbench.sv. Leave design.sv empty.');
      L.push('//   3. Tools & Simulators: pick one with SVA support,');
      L.push('//      for example Synopsys VCS, Cadence Xcelium or Aldec Riviera-PRO.');
      L.push('//   4. Tick "Open EPWave after run", then press Run.');
      L.push('// ------------------------------------------------------------------');
      L.push('');
      L.push('module apb_lab_checker #(parameter int NSEL = 1) (');
      L.push('  input logic            PCLK, PRESETn,');
      L.push('  input logic [NSEL-1:0] PSELx,');
      L.push('  input logic            PENABLE, PWRITE, PREADY, PSLVERR, PWAKEUP,');
      L.push('  input logic [31:0]     PADDR, PWDATA, PRDATA,');
      L.push('  input logic [3:0]      PSTRB,');
      L.push('  input logic [2:0]      PPROT');
      L.push(');');
      L.push('  default clocking cb @(posedge PCLK); endclocking');
      L.push('  default disable iff (!PRESETn);');
      L.push('');
      L.push('  logic sel, setup_ph, access_ph, wait_ph, done_ph;');
      L.push('  assign sel       = |PSELx;');
      L.push('  assign setup_ph  = sel && !PENABLE;');
      L.push('  assign access_ph = sel &&  PENABLE;');
      L.push('  assign wait_ph   = access_ph && !PREADY;');
      L.push('  assign done_ph   = access_ph &&  PREADY;');
      L.push('');
      ASSERTS.filter(a => ver >= a.ver).forEach(a => { L.push(`  // ${a.plain}`); a.sva.split('\n').forEach(s => L.push('  ' + s)); });
      if (withMine) { L.push(''); L.push('  // Your assertion from the builder'); customSVA(bd.a, bd.op, bd.c).split('\n').forEach(s => L.push('  ' + s)); }
      L.push('endmodule');
      L.push('');
      L.push('module tb;');
      L.push("  logic            PCLK = 1'b0;");
      L.push('  logic            PRESETn;');
      L.push(`  logic [${ns - 1}:0]      PSELx;`);
      L.push('  logic            PENABLE, PWRITE, PREADY, PSLVERR, PWAKEUP;');
      L.push('  logic [31:0]     PADDR, PWDATA, PRDATA;');
      L.push('  logic [3:0]      PSTRB;');
      L.push('  logic [2:0]      PPROT;');
      L.push('');
      L.push('  always #5 PCLK = ~PCLK;');
      L.push(`  apb_lab_checker #(.NSEL(${ns})) u_chk (.*);`);
      L.push('');
      L.push('  initial begin');
      L.push('    $dumpfile("dump.vcd"); $dumpvars(0, tb);');
      const fixed = [];
      if (ver < 3) fixed.push("PREADY = 1'b1;", "PSLVERR = 1'b0;");
      if (ver < 4) fixed.push("PSTRB = 4'b0000;", "PPROT = 3'b000;");
      if (ver < 5) fixed.push("PWAKEUP = 1'b0;");
      if (fixed.length) L.push(`    ${fixed.join(' ')}   // not part of APB${ver}`);
      const drive = ['PRESETn', 'PSELx', 'PENABLE', 'PWRITE', 'PADDR', 'PWDATA', 'PRDATA']
        .concat(ver >= 3 ? ['PREADY', 'PSLVERR'] : [], ver >= 4 ? ['PSTRB', 'PPROT'] : [], ver >= 5 ? ['PWAKEUP'] : []);
      const valOf = (c, n) => {
        if (n !== 'PSELx') return svVal(n, c[n]);
        return `${ns}'b${w.sels.slice().reverse().map(s => (isX(c[s]) ? 'x' : String(c[s] ? 1 : 0))).join('')}`;
      };
      const prev = {};
      C.forEach((c, i) => {
        L.push('');
        L.push(i === 0 ? `    #1;  // cycle 0 · ${PHLABEL[phaseOf(w, 0)]} · sampled at T1` : `    @(posedge PCLK); #1;  // cycle ${i} · ${PHLABEL[phaseOf(w, i)]} · sampled at T${i + 1}`);
        const parts = drive.filter(n => valOf(c, n) !== prev[n]).map(n => `${n} = ${valOf(c, n)};`);
        drive.forEach(n => { prev[n] = valOf(c, n); });
        for (let k = 0; k < parts.length; k += 3) L.push('    ' + parts.slice(k, k + 3).join(' '));
      });
      L.push('');
      L.push('    @(posedge PCLK); #1;');
      L.push(`    $display("PosEdge APB Lab: ${C.length} cycles driven. Assertion messages are above; the waveform is in EPWave.");`);
      L.push('    $finish;');
      L.push('  end');
      L.push('endmodule');
      return L.join('\n');
    }
    function renderExport() {
      if ($('#exp-panel').hidden) return;
      const code = exportSV($('#exp-mine').checked);
      $('#exp-code').innerHTML = hlSV(code);
      $('#exp-lines').textContent = `${code.split('\n').length} lines`;
    }
    $('#lab-export').addEventListener('click', () => {
      const p = $('#exp-panel'); p.hidden = !p.hidden;
      $('#lab-export').setAttribute('aria-expanded', String(!p.hidden));
      renderExport();
    });
    $('#exp-mine').addEventListener('change', renderExport);
    $('#exp-copy').addEventListener('click', e => copyText(exportSV($('#exp-mine').checked), e.currentTarget, $('#exp-code')));

    /* ----- transfer table ----- */
    const clampInt = (v, a, b) => Math.max(a, Math.min(b, parseInt(v, 10) || 0));
    function renderTable() {
      const v = cfg.ver;
      const cols = ['#', 'Type', 'Select', 'PADDR (hex)', 'Data (hex)'];
      if (v >= 3) cols.push('Wait states', 'PSLVERR');
      if (v >= 4) cols.push('PSTRB', 'PPROT');
      cols.push('Idle after', '');
      $('#lab-txhead').innerHTML = '<tr>' + cols.map(c => `<th scope="col">${c}</th>`).join('') + '</tr>';
      body.innerHTML = cfg.txns.map((t, k) => {
        const id = f => `tx${k}-${f}`;
        const gap = t.gap === undefined ? (k === cfg.txns.length - 1 ? 2 : 0) : t.gap;
        let r = `<tr><td class="num">${k + 1}</td>`;
        r += `<td><select id="${id('w')}" data-f="write" aria-label="Transfer ${k + 1} type"><option value="1"${t.write ? ' selected' : ''}>Write</option><option value="0"${t.write ? '' : ' selected'}>Read</option></select></td>`;
        r += `<td><select id="${id('s')}" data-f="slave" aria-label="Transfer ${k + 1} completer"><option value="1"${(t.slave || 1) === 1 ? ' selected' : ''}>PSEL1</option><option value="2"${t.slave === 2 ? ' selected' : ''}>PSEL2</option></select></td>`;
        r += `<td><input id="${id('a')}" data-f="addr" class="hex" value="${hexs(t.addr)}" spellcheck="false" autocomplete="off" aria-label="Transfer ${k + 1} address"></td>`;
        r += `<td><input id="${id('d')}" data-f="data" class="hex wide" value="${hexs(t.data)}" spellcheck="false" autocomplete="off" aria-label="Transfer ${k + 1} ${t.write ? 'write data' : 'read data returned'}" title="${t.write ? 'PWDATA driven by the requester' : 'PRDATA returned by the completer'}"></td>`;
        if (v >= 3) {
          r += `<td><input id="${id('wt')}" type="number" min="0" max="24" data-f="wait" value="${t.wait || 0}" aria-label="Transfer ${k + 1} wait states"></td>`;
          r += `<td class="ctr"><input id="${id('e')}" type="checkbox" data-f="err"${t.err ? ' checked' : ''} aria-label="Transfer ${k + 1} error response"></td>`;
        }
        if (v >= 4) {
          const sb = t.write ? (t.strb === undefined ? 15 : t.strb) : (t.strb || 0);
          r += `<td><input id="${id('st')}" data-f="strb" class="bin" maxlength="4" value="${sb.toString(2).padStart(4, '0')}" aria-label="Transfer ${k + 1} strobes, binary"></td>`;
          r += `<td><select id="${id('p')}" data-f="prot" aria-label="Transfer ${k + 1} protection">${[0, 1, 2, 3, 4, 5, 6, 7].map(p => `<option value="${p}"${(t.prot || 0) === p ? ' selected' : ''}>${p.toString(2).padStart(3, '0')}</option>`).join('')}</select></td>`;
        }
        r += `<td><input id="${id('g')}" type="number" min="0" max="8" data-f="gap" value="${gap}" aria-label="Idle cycles after transfer ${k + 1}"></td>`;
        r += `<td><button type="button" class="icon-btn" data-del="${k}" aria-label="Remove transfer ${k + 1}"${cfg.txns.length < 2 ? ' disabled' : ''}>×</button></td></tr>`;
        return r;
      }).join('');
      $('#lab-wake-wrap').hidden = v < 5;
      $('#lab-txadd-note').textContent = v === 2 ? 'APB2 has no PREADY or PSLVERR, so every transfer takes exactly two cycles.' : v === 3 ? 'APB3 adds wait states and the error response.' : v === 4 ? 'APB4 adds PSTRB (binary, bit 0 = byte lane 0; reads must be 0000) and PPROT.' : 'APB5 adds PWAKEUP. Set how many cycles it leads PSEL.';
    }
    function regen(keep) { show(generate(cfg), keep); setEdited(false); }
    function setEdited(v, label) {
      badge.hidden = !v || mode !== 'edit';
      if (v) $('#lab-badge-t').textContent = label || 'Edited by hand. The transfer table no longer matches the waveform.';
    }
    function toCustom() { clearBug(); src = { kind: 'custom' }; ref = null; scenario = null; renderScenario(); setNow('Your own transfers'); }
    body.addEventListener('change', e => {
      const el = e.target, f = el.dataset.f; if (!f) return;
      const k = Array.from(body.children).indexOf(el.closest('tr'));
      const t = cfg.txns[k]; let ok = true;
      switch (f) {
        case 'write': t.write = +el.value; if (!t.write) t.strb = 0; else if (!t.strb) t.strb = 15; break;
        case 'slave': t.slave = +el.value; break;
        case 'addr': case 'data': {
          const s = el.value.trim().replace(/^0x/i, '').replace(/_/g, '');
          if (/^[0-9a-f]{1,8}$/i.test(s)) t[f] = parseInt(s, 16) >>> 0; else ok = false;
          break;
        }
        case 'wait': t.wait = clampInt(el.value, 0, 24); break;
        case 'gap': t.gap = clampInt(el.value, 0, 8); break;
        case 'err': t.err = el.checked ? 1 : 0; break;
        case 'strb': { const s = el.value.trim(); if (/^[01]{1,4}$/.test(s)) t.strb = parseInt(s, 2); else ok = false; break; }
        case 'prot': t.prot = +el.value; break;
      }
      el.classList.toggle('invalid', !ok);
      el.setAttribute('aria-invalid', String(!ok));
      if (!ok) return;
      toCustom();
      regen(true);
      if (f === 'write' || f === 'wait' || f === 'gap') renderTable();
    });
    body.addEventListener('click', e => {
      const b = e.target.closest('[data-del]'); if (!b) return;
      cfg.txns.splice(+b.dataset.del, 1); toCustom(); renderTable(); regen();
    });
    function addTxn(write) {
      const prev = cfg.txns[cfg.txns.length - 1];
      if (prev && prev.gap === undefined) prev.gap = 0;
      const addr = prev ? ((prev.addr + 4) >>> 0) : 0x10;
      cfg.txns.push({ write, addr, data: write ? 0x00001000 + cfg.txns.length : 0xC0DE0000 + cfg.txns.length, wait: cfg.ver >= 3 ? 1 : 0, slave: prev ? prev.slave : 1 });
      toCustom(); renderTable(); regen();
    }
    $('#lab-addw').addEventListener('click', () => addTxn(1));
    $('#lab-addr').addEventListener('click', () => addTxn(0));

    function loadPreset(id) {
      const p = presetById(id); if (!p) return;
      stopPlay(); clearBug();
      cfg = clone(p.cfg); scenario = id; lastScenario = id;
      src = { kind: 'scenario' }; ref = null;
      verSel.value = String(cfg.ver);
      $('#lab-rst').value = cfg.reset || 0;
      $('#lab-wake').value = cfg.wake === undefined ? 1 : cfg.wake;
      if (applied !== '__mine__') applied = p.focus;
      renderTable(); renderScenario(); setNow(`Scenario: ${p.name}`);
      regen();
    }
    function setVersion(v) {
      verSel.value = String(v);
      cfg.ver = v;
      if (cfg.ver >= 5 && cfg.wake === undefined) cfg.wake = 1;
      cov = newCov(); runsDone = 0; lastRun = null;
      toCustom(); renderTable(); regen();
      renderCons(); renderCov(); $('#rc-res-wrap').hidden = true; $('#rc-notes').innerHTML = '';
    }
    verSel.addEventListener('change', () => setVersion(+verSel.value));
    $('#lab-rst').addEventListener('change', e => { cfg.reset = clampInt(e.target.value, 0, 6); toCustom(); regen(); });
    $('#lab-wake').addEventListener('change', e => { cfg.wake = clampInt(e.target.value, 0, 4); toCustom(); regen(); });
    $('#lab-zoom').addEventListener('input', e => ctl.setCW(+e.target.value));
    $('#lab-regen').addEventListener('click', () => { renderTable(); regen(); });
    $('#edit-reset').addEventListener('click', () => { if (ref && src.kind === 'edit') { const w = ref; ref = null; src = { kind: scenario ? 'scenario' : 'custom' }; setEdited(false); show(clone(w), true); } });

    /* ----- playback ----- */
    const playBtn = $('#lab-play');
    function stopPlay() { if (playT) clearInterval(playT); playT = null; playBtn.textContent = '▶ Play'; playBtn.setAttribute('aria-pressed', 'false'); }
    playBtn.addEventListener('click', () => {
      if (playT) { stopPlay(); return; }
      if (ctl.cursor >= ctl.wave.cycles.length - 1) ctl.setCursor(-1);
      playBtn.textContent = '❚❚ Pause'; playBtn.setAttribute('aria-pressed', 'true');
      const step = () => {
        if (ctl.cursor >= ctl.wave.cycles.length - 1) { stopPlay(); return; }
        ctl.setCursor(ctl.cursor + 1, true); ctl.ensureVisible();
      };
      step(); playT = setInterval(step, 1500);
    });
    $('#lab-prev').addEventListener('click', () => { stopPlay(); ctl.setCursor(Math.max(0, ctl.cursor - 1), true); ctl.ensureVisible(); });
    $('#lab-next').addEventListener('click', () => { stopPlay(); ctl.setCursor(Math.min(ctl.wave.cycles.length - 1, ctl.cursor + 1), true); ctl.ensureVisible(); });

    /* ----- direct signal editing ----- */
    let popTarget = null;
    function closePop() { pop.hidden = true; popTarget = null; }
    function startEdit() {
      if (src.kind !== 'edit') { const before = clone(ctl.wave); clearBug(); src = { kind: 'edit' }; ref = before; setNow((scenario ? 'Scenario ' + presetById(scenario).short : 'Waveform') + ', edited by hand'); }
    }
    ctl.onCell = (lane, i, e) => {
      const c = ctl.wave.cycles[i];
      if (SIG[lane].w === 1) {
        startEdit();
        c[lane] = c[lane] === 1 ? 0 : 1;
        setEdited(true); show(ctl.wave, true); return;
      }
      popTarget = { lane, i };
      const r = stage.getBoundingClientRect();
      const bin = lane === 'PSTRB' || lane === 'PPROT';
      $('#lab-pop-l').textContent = `${lane} in cycle ${i} (${bin ? 'binary' : 'hex'}, or x)`;
      const inp = $('#lab-pop-i');
      inp.value = isX(c[lane]) ? 'x' : fmt(lane, c[lane]);
      pop.hidden = false;
      const left = Math.min(Math.max(8, e.clientX - r.left - 20), r.width - pop.offsetWidth - 8);
      pop.style.left = left + 'px';
      pop.style.top = (e.clientY - r.top + 14) + 'px';
      inp.focus(); inp.select();
    };
    function applyPop(val) {
      if (!popTarget) return;
      const { lane, i } = popTarget;
      const bin = lane === 'PSTRB' || lane === 'PPROT';
      const v = String(val).trim().replace(/^0x/i, '').replace(/_/g, '');
      let out;
      if (/^x$/i.test(v)) out = 'x';
      else if (bin && /^[01]+$/.test(v)) out = parseInt(v, 2);
      else if (!bin && /^[0-9a-f]{1,8}$/i.test(v)) out = parseInt(v, 16) >>> 0;
      else { $('#lab-pop-i').classList.add('invalid'); return; }
      $('#lab-pop-i').classList.remove('invalid');
      startEdit();
      ctl.wave.cycles[i][lane] = out;
      setEdited(true); show(ctl.wave, true); closePop();
    }
    $('#lab-pop-ok').addEventListener('click', () => applyPop($('#lab-pop-i').value));
    $('#lab-pop-x').addEventListener('click', () => applyPop('x'));
    $('#lab-pop-c').addEventListener('click', closePop);
    $('#lab-pop-i').addEventListener('keydown', e => { if (e.key === 'Enter') applyPop(e.target.value); if (e.key === 'Escape') closePop(); });

    renderBugPick();
    renderCons();
    renderCov();
    loadPreset('apb2-write');
    setMode('build');

    return {
      loadPreset(id) { loadPreset(id); },
      insertBug,
      loadWave(w, label) {
        stopPlay(); clearBug();
        cfg = { ver: w.ver, txns: [{ write: 1, addr: 0x10, data: 0x1 }] };
        verSel.value = String(w.ver); renderTable();
        src = { kind: 'edit', label: `From the bug hunt “${label}”. Click cells on the waveform to fix it until every assertion passes.` }; ref = null; scenario = null;
        renderScenario(); setNow(`Bug hunt: ${label}`);
        setMode('edit');
        show(clone(w));
        toWorkbench();
      }
    };
  }

  /* ================================================================
     15. Version cards
     ================================================================ */
  function initVersions(lab) {
    $$('.ver-wave').forEach(el => {
      const p = presetById(el.dataset.preset); if (!p) return;
      const ctl = Wave(el, { cw: 44, compact: true });
      ctl.set(generate(clone(p.cfg)));
      const ro = el.parentElement.querySelector('.ver-ro');
      if (ro) Readout(ro, ctl, { values: false, empty: 'Hover the waveform to see what each cycle does.' });
    });
    $$('[data-open-preset]').forEach(b => b.addEventListener('click', () => {
      if (!lab) return;
      lab.loadPreset(b.dataset.openPreset);
      scrollToId('step2');
    }));
    $$('[data-break]').forEach(b => b.addEventListener('click', () => {
      if (!lab) return;
      lab.insertBug(b.dataset.break);
    }));
  }

  /* ================================================================
     16. Rules table (generated from the assertion model)
     ================================================================ */
  function initRules() {
    const tb = $('#rules-body'); if (!tb) return;
    tb.innerHTML = ASSERTS.map(a => `<tr><td class="mono">${a.name}</td><td><span class="as-tag">${a.tag}</span>${a.ver > 2 ? ` <span class="muted small">APB${a.ver}+</span>` : ''}</td><td>${esc(a.meaning)}</td><td class="mono small">${esc(a.op === 'always' ? a.cons : a.ante + '  ' + a.op + '  ' + a.cons)}</td><td><span class="sev ${a.sev === 'error' ? 'e' : 'w'}">${a.sev === 'error' ? 'error' : 'warning'}</span></td></tr>`).join('');
  }

  /* ================================================================
     17. Spot-the-bug puzzles
     ================================================================ */
  function initPuzzles(lab) {
    if (!$('#pz')) return;
    const ctl = Wave($('#pz-wave'), { cw: 50, showViol: false, phase: false });
    Readout($('#pz-ro'), ctl, { explain: false, empty: 'Hover to read signal values. Click the cycle you think is wrong, or focus the waveform, move with the arrow keys and press Enter.' });
    const fb = $('#pz-fb');
    let k = 0, tries = 0, revealed = false;
    const solved = new Set(store.get('pz', []));
    const answerSet = w => new Set(check(w).filter(v => v.sev === 'error').map(v => v.i));

    function nav() {
      $('#pz-nav').innerHTML = PUZZLES.map((p, i) => `<button type="button" data-i="${i}" class="${i === k ? 'cur' : ''} ${solved.has(i) ? 'done' : ''}" aria-label="Puzzle ${i + 1}${solved.has(i) ? ', solved' : ''}" aria-current="${i === k}">${i + 1}</button>`).join('');
    }
    function show(i) {
      k = i; tries = 0; revealed = false;
      const p = PUZZLES[k];
      $('#pz-title').textContent = `${k + 1}. ${p.title}`;
      $('#pz-ver').textContent = 'APB' + p.wave.ver;
      fb.className = 'pz-fb'; fb.innerHTML = 'One cycle in this waveform breaks the protocol. Click the column where the violation first shows up.';
      ctl.setShowViol(false);
      ctl.set(clone(p.wave));
      nav();
    }
    function reveal(msg, cls) {
      revealed = true;
      ctl.setShowViol(true);
      const first = Math.min.apply(null, Array.from(answerSet(ctl.wave)));
      ctl.setCursor(first, true); ctl.ensureVisible();
      fb.className = 'pz-fb ' + cls;
      fb.innerHTML = msg;
    }
    ctl.onPick = i => {
      const p = PUZZLES[k];
      if (revealed) { ctl.setCursor(i, true); return; }
      ctl.setCursor(i, true);
      if (answerSet(ctl.wave).has(i)) {
        solved.add(k); store.set('pz', Array.from(solved)); nav(); progress();
        reveal(`<b>Correct: cycle ${i}, sampled at T${i + 1}.</b> ${p.explain}`, 'ok');
      } else {
        tries++;
        fb.className = 'pz-fb no';
        fb.innerHTML = `<b>Cycle ${i} is legal.</b> ` + (tries >= 2 ? `Hint: ${p.hint}` : 'Check each signal against the rule for the phase the bus is in.');
      }
    };
    $('#pz-nav').addEventListener('click', e => { const b = e.target.closest('button'); if (b) show(+b.dataset.i); });
    $('#pz-show').addEventListener('click', () => reveal(`<b>Answer.</b> ${PUZZLES[k].explain}`, 'shown'));
    $('#pz-nextb').addEventListener('click', () => show((k + 1) % PUZZLES.length));
    $('#pz-fix').addEventListener('click', () => {
      if (!lab) return;
      lab.loadWave(PUZZLES[k].wave, PUZZLES[k].title);
    });
    const firstOpen = PUZZLES.findIndex((_, i) => !solved.has(i));
    show(firstOpen < 0 ? 0 : firstOpen);
  }

  /* ================================================================
     18. Exercise checklist persistence
     ================================================================ */
  function initExercises() {
    const done = new Set(store.get('ex', []));
    $$('input.ex-done').forEach(cb => {
      cb.checked = done.has(cb.dataset.ex);
      cb.addEventListener('change', () => {
        if (cb.checked) done.add(cb.dataset.ex); else done.delete(cb.dataset.ex);
        store.set('ex', Array.from(done)); progress();
      });
    });
  }

  /* ================================================================
     19. Multiple-choice engine (checkpoint and quiz)
     ================================================================ */
  const md = s => esc(s).replace(/`([^`]+)`/g, '<code>$1</code>');
  function initCheckpoint() {
    const host = $('#cp-box'); if (!host) return;
    let k = 0, score = 0;
    function render() {
      if (k >= CHECKPOINT.length) {
        const all = score === CHECKPOINT.length;
        host.innerHTML = `<div class="qz-done"><p class="qz-big">${score} / ${CHECKPOINT.length}</p><p>${all ? '<b>That is the core of APB, and you have it.</b> Everything from here adds detail, not new ideas. Stage 2 lets you play with real waveforms.' : 'Close. Step through the state machine once more, then try again.'}</p><div class="qz-nav"><button type="button" class="btn" id="cp-again">Try again</button>${all ? '<button type="button" class="btn primary" id="cp-on">Go to the waveform lab →</button>' : ''}</div></div>`;
        if (all) markDone('checkpoint', false);
        $('#cp-again', host).addEventListener('click', () => { k = 0; score = 0; render(); });
        const on = $('#cp-on', host); if (on) on.addEventListener('click', () => scrollToId('lab'));
        return;
      }
      const q = CHECKPOINT[k];
      host.innerHTML = `<div class="qz-top"><span>Question ${k + 1} of ${CHECKPOINT.length}</span><span class="qz-score">Score ${score}</span></div>
        <div class="qz-bar" aria-hidden="true"><i style="width:${(k / CHECKPOINT.length) * 100}%"></i></div>
        <p class="qz-q">${md(q.q)}</p>
        <div class="qz-opts" role="group" aria-label="Answers">${q.o.map((o, i) => `<button type="button" class="qz-opt" data-i="${i}"><span class="qz-key">${'ABCD'[i]}</span><span>${md(o)}</span></button>`).join('')}</div>
        <div class="qz-exp" hidden></div>
        <div class="qz-nav"><button type="button" class="btn primary" id="cp-next" hidden>${k === CHECKPOINT.length - 1 ? 'See result' : 'Next question'}</button></div>`;
      $$('.qz-opt', host).forEach(b => b.addEventListener('click', () => {
        const i = +b.dataset.i, ok = i === q.a;
        if (ok) score++;
        $$('.qz-opt', host).forEach(x => { const j = +x.dataset.i; x.disabled = true; if (j === q.a) x.classList.add('right'); else if (j === i) x.classList.add('wrong'); });
        const ex = $('.qz-exp', host); ex.hidden = false; ex.className = 'qz-exp ' + (ok ? 'ok' : 'no');
        ex.innerHTML = `<b>${ok ? 'Correct.' : 'Not quite.'}</b> ${md(q.e)}`;
        const nb = $('#cp-next', host); nb.hidden = false; nb.focus();
      }));
      $('#cp-next', host).addEventListener('click', () => { k++; render(); });
    }
    render();
  }

  function initQuiz() {
    const host = $('#quiz-box'); if (!host) return;
    const LV = { b: 'Basic', i: 'Intermediate', a: 'Advanced' };
    let pool = [], idx = 0, score = 0, wrong = [], level = 'all';
    function start(list) { pool = list; idx = 0; score = 0; wrong = []; render(); }
    function startLevel() { start(shuffle(QUIZ.filter(q => level === 'all' || q.l === level))); }
    function render() {
      if (idx >= pool.length) { finish(); return; }
      const q = pool[idx];
      host.innerHTML = `<div class="qz-top"><span>Question ${idx + 1} of ${pool.length}</span><span class="lvl lvl-${q.l}">${LV[q.l]}</span><span class="qz-score">Score ${score}</span></div>
        <div class="qz-bar" aria-hidden="true"><i style="width:${(idx / pool.length) * 100}%"></i></div>
        <p class="qz-q">${md(q.q)}</p>
        <div class="qz-opts" role="group" aria-label="Answers">${q.o.map((o, i) => `<button type="button" class="qz-opt" data-i="${i}"><span class="qz-key">${'ABCD'[i]}</span><span>${md(o)}</span></button>`).join('')}</div>
        <div class="qz-exp" hidden></div>
        <div class="qz-nav"><button type="button" class="btn primary" id="qz-next" hidden>${idx === pool.length - 1 ? 'See results' : 'Next question'}</button></div>`;
      $$('.qz-opt', host).forEach(b => b.addEventListener('click', () => choose(+b.dataset.i)));
      $('#qz-next', host).addEventListener('click', () => { idx++; render(); });
    }
    function choose(i) {
      const q = pool[idx];
      const ok = i === q.a;
      if (ok) score++; else wrong.push(q);
      $$('.qz-opt', host).forEach(b => {
        const j = +b.dataset.i; b.disabled = true;
        if (j === q.a) b.classList.add('right');
        else if (j === i) b.classList.add('wrong');
      });
      const ex = $('.qz-exp', host);
      ex.hidden = false;
      ex.className = 'qz-exp ' + (ok ? 'ok' : 'no');
      ex.innerHTML = `<b>${ok ? 'Correct.' : 'Not quite.'}</b> ${md(q.e)}`;
      $('.qz-score', host).textContent = `Score ${score}`;
      const nb = $('#qz-next', host); nb.hidden = false; nb.focus();
    }
    function finish() {
      const pct = Math.round((score / pool.length) * 100);
      const best = store.get('quizBest', 0);
      if (pool.length >= 10 && pct > best) store.set('quizBest', pct);
      progress();
      const msg = pct >= 90 ? 'Interview-ready on APB. Move on to AHB or AXI.' : pct >= 70 ? 'Solid. Review the explanations for the ones you missed.' : 'Go back through the state machine and the lab, then try again.';
      host.innerHTML = `<div class="qz-done"><p class="qz-big">${score} / ${pool.length}</p><p>${pct}% · ${msg}</p>
        ${wrong.length ? `<details class="qz-review"><summary>Review the ${wrong.length} you missed</summary><ol>${wrong.map(q => `<li><p>${md(q.q)}</p><p class="muted">Answer: ${md(q.o[q.a])}. ${md(q.e)}</p></li>`).join('')}</ol></details>` : ''}
        <div class="qz-nav">${wrong.length ? '<button type="button" class="btn primary" id="qz-retry">Retry the ones I missed</button>' : ''}<button type="button" class="btn" id="qz-restart">Start again</button></div></div>`;
      const r = $('#qz-retry', host); if (r) r.addEventListener('click', () => start(shuffle(wrong)));
      $('#qz-restart', host).addEventListener('click', startLevel);
    }
    $('#quiz-level').addEventListener('click', e => {
      const b = e.target.closest('button'); if (!b) return;
      level = b.dataset.lvl;
      $$('#quiz-level button').forEach(x => x.setAttribute('aria-pressed', String(x === b)));
      startLevel();
    });
    startLevel();
  }

  /* ================================================================
     20. Roadmap, chapters, progress
     ================================================================ */
  function markDone(id, go) {
    const d = new Set(store.get('ch', []));
    d.add(id); store.set('ch', Array.from(d));
    renderChapters(); progress();
    if (go) {
      const k = CHAPTERS.findIndex(c => c.id === id), nx = CHAPTERS[k + 1];
      scrollToId(nx ? nx.id : 'roadmap');
    }
  }
  function renderRoad(d) {
    const host = $('#road'); if (!host) return;
    const next = CHAPTERS.find(c => !d.has(c.id));
    host.innerHTML = STAGES.map(s => {
      const chs = CHAPTERS.filter(c => c.stage === s.n);
      const nd = chs.filter(c => d.has(c.id)).length, min = chs.reduce((a, c) => a + c.min, 0);
      const cur = next && next.stage === s.n;
      return `<article class="stage${nd === chs.length ? ' complete' : ''}${cur ? ' current' : ''}">
        <div class="stage-top"><span class="stage-n">Stage ${s.n}${cur ? ' · you are here' : nd === chs.length ? ' · done' : ''}</span><span>about ${min} min</span></div>
        <h3>${s.name}</h3><p>${s.what}</p>
        <ol>${chs.map(c => `<li class="${d.has(c.id) ? 'done' : ''}"><a href="#${c.id}">${c.name}</a><span>${c.min} min</span></li>`).join('')}</ol>
        <div class="stage-bar" aria-label="${nd} of ${chs.length} chapters done"><i style="width:${nd / chs.length * 100}%"></i></div></article>`;
    }).join('');
    const go = $('#road-go');
    go.textContent = d.size === 0 ? 'Start with Basics →' : next ? `Continue: ${next.name} →` : 'All done · take the quiz again →';
    go.dataset.target = next ? next.id : 'quiz';
    $('#road-sum').textContent = d.size === 0 ? 'Stages 1 and 2 teach the whole protocol in about 45 minutes.' : `${d.size} of ${CHAPTERS.length} chapters done. Progress is saved in this browser.`;
  }
  function renderChapters() {
    const d = new Set(store.get('ch', []));
    $$('.ch-done').forEach(b => {
      const k = CHAPTERS.findIndex(c => c.id === b.dataset.ch), nx = CHAPTERS[k + 1], isD = d.has(b.dataset.ch);
      b.textContent = (isD ? 'Done ✓ · ' : 'Mark done · ') + (nx ? `Next: ${nx.name} →` : 'Back to the roadmap ↑');
      b.classList.toggle('is-done', isD);
    });
    $$('.rail nav a[href]').forEach(a => a.classList.toggle('done', d.has(a.getAttribute('href').slice(1))));
    renderRoad(d);
  }
  function initChapters() {
    CHAPTERS.forEach(ch => {
      const sec = document.getElementById(ch.id); if (!sec) return;
      const no = sec.querySelector('.sec-head .sec-no');
      if (no) no.insertAdjacentHTML('beforeend', ` <span class="sec-time">Stage ${ch.stage} · about ${ch.min} min</span> <button type="button" class="listen" data-listen="${ch.id}" aria-label="Listen to a short guide to ${esc(ch.name)}"><svg width="13" height="13" viewBox="0 0 16 16" aria-hidden="true"><path d="M2 6h3l4-3v10l-4-3H2z" fill="currentColor"/><path d="M11 5.5a3.5 3.5 0 0 1 0 5M12.8 3.5a6 6 0 0 1 0 9" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/></svg>Listen</button>`);
      const end = document.createElement('div');
      end.className = 'sec-end';
      end.innerHTML = (ch.rem ? `<p class="remember"><span>Remember</span>${esc(ch.rem)}</p>` : '<p class="remember"></p>') + `<button type="button" class="btn primary ch-done" data-ch="${ch.id}"></button>`;
      sec.appendChild(end);
    });
    document.addEventListener('click', e => { const b = e.target.closest('.ch-done'); if (b) markDone(b.dataset.ch, true); });
    $('#road-go').addEventListener('click', e => scrollToId(e.currentTarget.dataset.target || 'basics'));
    renderChapters();
  }
  function progress() {
    const set = (id, t) => { const el = $(id); if (el) el.textContent = t; };
    const ch = store.get('ch', []).length;
    set('#prog-ch', `${ch}/${CHAPTERS.length}`);
    const bar = $('#prog-bar'); if (bar) bar.style.width = (ch / CHAPTERS.length * 100) + '%';
    set('#prog-bugs', `${store.get('bugs', []).length}/${BUGS.length}`);
    set('#prog-pz', `${store.get('pz', []).length}/${PUZZLES.length}`);
    set('#prog-dr', `${store.get('drill', []).length}/${DRILLS.length}`);
    const qb = store.get('quizBest', 0);
    set('#prog-qz', qb ? qb + '%' : '–');
  }

  function initNav() {
    const links = $$('.rail nav a');
    if (!('IntersectionObserver' in window)) return;
    const map = new Map(links.map(a => [a.getAttribute('href').slice(1), a]));
    const io = new IntersectionObserver(entries => {
      entries.forEach(en => {
        if (en.isIntersecting) {
          links.forEach(a => a.classList.remove('active'));
          const a = map.get(en.target.id);
          if (a) { a.classList.add('active'); if (window.innerWidth < 900) a.parentElement.scrollLeft = a.offsetLeft - 40; }
        }
      });
    }, { rootMargin: '-35% 0px -60% 0px' });
    $$('main section[id]').forEach(s => io.observe(s));
  }

  /* ================================================================
     21b. Site footer from the settings on <main>, and deep links
     ================================================================ */
  function initSite() {
    const d = ($('main') || {}).dataset || {};
    const a = (href, text) => `<a href="${esc(href)}" target="_blank" rel="noopener">${esc(text)}</a>`;
    if (d.authorName) $('#sf-by').innerHTML = `Built by ${d.authorUrl ? a(d.authorUrl, d.authorName) : esc(d.authorName)}, a design verification engineer, for students, freshers and engineers preparing for verification roles.`;
    const links = [];
    if (d.pageUrl) links.push(a(d.pageUrl, 'PosEdge on LinkedIn'));
    if (d.uvmUrl) links.push(a(d.uvmUrl, 'Full UVM testbench'));
    if (d.githubUrl) links.push(a(d.githubUrl, 'Source on GitHub'));
    if (d.feedbackUrl) links.push(a(d.feedbackUrl, 'Send feedback'));
    $('#sf-links').innerHTML = links.join('');
    const notify = d.notifyUrl || d.feedbackUrl;
    if (notify) { const n = $('#sf-notify'); n.href = notify; n.hidden = false; }
    $('#sf-follow').innerHTML = d.pageUrl ? `Or follow ${a(d.pageUrl, 'PosEdge on LinkedIn')} for new labs.` : '';
  }
  function initDeepLinks(lab) {
    if (!lab) return;
    const route = () => {
      const h = (location.hash || '').slice(1);
      if (/^bug-[a-z0-9-]+$/.test(h) && BUGS.some(b => b.id === h.slice(4))) lab.insertBug(h.slice(4));
      else if (/^scenario-[a-z0-9-]+$/.test(h) && presetById(h.slice(9))) { lab.loadPreset(h.slice(9)); scrollToId('step2'); }
    };
    window.addEventListener('hashchange', route);
    setTimeout(route, 60);
  }

  /* ================================================================
     22. Draw it: interview drill
     ================================================================ */
  function initDrill() {
    const grid = $('#dr-grid'); if (!grid) return;
    const solved = new Set(store.get('drill', []));
    let k = 0, user = null, w = null, graded = null, shown = false, painting = null;
    const LV = { b: 'Basic', i: 'Intermediate', a: 'Advanced' };
    function nav() {
      $('#dr-nav').innerHTML = DRILLS.map((d, i) => `<button type="button" data-i="${i}" class="${i === k ? 'cur' : ''} ${solved.has(d.id) ? 'done' : ''}" aria-label="Drill ${i + 1}${solved.has(d.id) ? ', solved' : ''}" aria-current="${i === k}">${i + 1}</button>`).join('');
    }
    function load(i) {
      k = i; const d = DRILLS[k];
      w = generate(clone(d.cfg)); graded = null; shown = false;
      user = {}; d.draw.forEach(s => { user[s] = w.cycles.map(() => (s === 'PRESETn' ? 1 : 0)); });
      $('#dr-lvl').className = 'lvl lvl-' + d.lvl; $('#dr-lvl').textContent = LV[d.lvl];
      $('#dr-title').textContent = `${k + 1}. ${d.title}`;
      $('#dr-text').textContent = d.task;
      $('#dr-meta').textContent = `APB${d.cfg.ver} · ${w.cycles.length} clock cycles · draw ${d.draw.join(', ')}`;
      $('#dr-fb').className = 'pz-fb'; $('#dr-fb').innerHTML = 'Click a cell to flip it between low and high. With a mouse you can also drag along a row to paint.';
      nav(); render();
    }
    function cellClass(s, i) {
      const d = DRILLS[k], v = shown ? (w.cycles[i][s] === 1 ? 1 : 0) : user[s][i];
      const prev = i > 0 ? (shown ? (w.cycles[i - 1][s] === 1 ? 1 : 0) : user[s][i - 1]) : v;
      let c = 'dr-c ' + (v ? 'hi' : 'lo') + (prev !== v ? ' edge' : '') + ' g-' + SIG[s].grp;
      if (drillDC(w, s, i)) c += ' dc';
      if (graded && !shown && !drillDC(w, s, i)) c += graded.wrong.some(x => x.s === s && x.i === i) ? ' bad' : ' good';
      return c;
    }
    function render() {
      const d = DRILLS[k], n = w.cycles.length;
      grid.style.gridTemplateColumns = `86px repeat(${n}, 46px)`;
      let h = '<span class="dr-h"></span>' + w.cycles.map((_, i) => `<span class="dr-h">${i}</span>`).join('');
      h += '<span class="dr-l g-clk">PCLK</span>' + w.cycles.map(() => '<span class="dr-clk" aria-hidden="true"></span>').join('');
      d.draw.forEach(s => {
        h += `<span class="dr-l g-${SIG[s].grp}">${s}</span>`;
        h += w.cycles.map((_, i) => {
          const dc = drillDC(w, s, i);
          const v = shown ? (w.cycles[i][s] === 1 ? 1 : 0) : user[s][i];
          return `<button type="button" class="${cellClass(s, i)}" data-s="${s}" data-i="${i}"${dc || shown ? ' disabled' : ''} aria-label="${s}, cycle ${i}: ${dc ? "don't care" : v ? 'high' : 'low'}"></button>`;
        }).join('');
      });
      grid.innerHTML = h;
    }
    function set(s, i, v) { if (drillDC(w, s, i) || shown) return; user[s][i] = v; graded = null; render(); }
    grid.addEventListener('pointerdown', e => {
      const b = e.target.closest('.dr-c'); if (!b || b.disabled) return;
      const s = b.dataset.s, i = +b.dataset.i, v = user[s][i] ? 0 : 1;
      if (e.pointerType === 'mouse') painting = { s, v };
      set(s, i, v);
      e.preventDefault();
    });
    grid.addEventListener('pointerover', e => {
      if (!painting) return;
      const b = e.target.closest('.dr-c'); if (!b || b.dataset.s !== painting.s) return;
      set(painting.s, +b.dataset.i, painting.v);
    });
    window.addEventListener('pointerup', () => { painting = null; });
    grid.addEventListener('keydown', e => {
      if (e.key !== 'Enter' && e.key !== ' ') return;
      const b = e.target.closest('.dr-c'); if (!b || b.disabled) return;
      e.preventDefault(); const s = b.dataset.s, i = +b.dataset.i; set(s, i, user[s][i] ? 0 : 1);
      const nb = grid.querySelector(`.dr-c[data-s="${s}"][data-i="${i}"]`); if (nb) nb.focus();
    });
    $('#dr-check').addEventListener('click', () => {
      if (shown) return;
      const d = DRILLS[k];
      graded = gradeDrill(d, user); render();
      const fb = $('#dr-fb');
      if (!graded.wrong.length) {
        solved.add(d.id); store.set('drill', Array.from(solved)); nav(); progress();
        fb.className = 'pz-fb ok'; fb.innerHTML = '<b>Correct.</b> Every cell that APB samples matches. You could draw this one on a whiteboard.';
        return;
      }
      const rules = [];
      graded.viol.forEach(v => { if (!rules.some(r => r.rule === v.rule)) rules.push(v); });
      fb.className = 'pz-fb no';
      fb.innerHTML = `<b>${graded.wrong.length} cell${graded.wrong.length > 1 ? 's are' : ' is'} wrong</b> (outlined in red).` +
        (rules.length ? ` Your drawing also breaks the protocol:<ul class="dr-rules">${rules.slice(0, 3).map(v => `<li><code>${v.rule}</code> at T${v.i + 1}: ${esc(AMAP[v.rule].plain)}</li>`).join('')}</ul>`
          : ' Your drawing is legal APB, but it does not match the task. Count the wait states, and check which cycle the transfer starts in.');
    });
    $('#dr-clear').addEventListener('click', () => load(k));
    $('#dr-show').addEventListener('click', () => {
      shown = !shown; render();
      $('#dr-show').textContent = shown ? 'Hide answer' : 'Show answer';
      if (shown) { $('#dr-fb').className = 'pz-fb shown'; $('#dr-fb').innerHTML = '<b>The answer.</b> Compare it with your drawing, then press <b>Hide answer</b> and try again.'; }
    });
    $('#dr-next').addEventListener('click', () => { $('#dr-show').textContent = 'Show answer'; load((k + 1) % DRILLS.length); });
    $('#dr-nav').addEventListener('click', e => { const b = e.target.closest('button'); if (b) { $('#dr-show').textContent = 'Show answer'; load(+b.dataset.i); } });
    const first = DRILLS.findIndex(d => !solved.has(d.id));
    load(first < 0 ? 0 : first);
  }

  /* ================================================================
     23. Voice guide
     ================================================================ */
  function initGuide() {
    const fab = $('#vg-fab'), panel = $('#vg-panel'); if (!fab) return;
    const synth = ('speechSynthesis' in window && typeof window.SpeechSynthesisUtterance === 'function') ? window.speechSynthesis : null;
    const ORDER = ['top', 'roadmap'].concat(CHAPTERS.map(c => c.id));
    const title = id => (id === 'top' ? 'Welcome' : id === 'roadmap' ? 'Your roadmap' : (CHAPTERS.find(c => c.id === id) || {}).name || id);
    const script = id => { const ch = CHAPTERS.find(c => c.id === id); return (GUIDE[id] || '') + (ch && ch.rem ? ' Remember: ' + ch.rem : ''); };
    const sentences = t => t.match(/[^.!?]+[.!?]+(\s|$)/g) || [t];
    let cur = 'top', inView = 'top', playing = false, paused = false, token = 0, voices = [], followT = null;
    const follow = $('#vg-follow'), rateSel = $('#vg-rate'), voiceSel = $('#vg-voice');
    follow.checked = store.get('vgFollow', false);
    rateSel.value = String(store.get('vgRate', 1));
    function caption(id, k) {
      $('#vg-sec').textContent = title(id);
      $('#vg-cap').innerHTML = sentences(script(id)).map((s, i) => `<span class="${i === k ? 'on' : ''}">${esc(s.trim())}</span>`).join(' ');
      const ix = ORDER.indexOf(id);
      $('#vg-prev').disabled = ix <= 0; $('#vg-next').disabled = ix >= ORDER.length - 1;
    }
    function setBtn() {
      $('#vg-play').textContent = !playing ? '▶ Play' : paused ? '▶ Resume' : '❚❚ Pause';
      $('#vg-play').setAttribute('aria-pressed', String(playing && !paused));
      fab.classList.toggle('speaking', playing && !paused);
    }
    function loadVoices() {
      if (!synth) return;
      voices = synth.getVoices().filter(v => /^en/i.test(v.lang));
      const saved = store.get('vgVoice', '');
      const pref = voices.find(v => v.name === saved) || voices.find(v => /en[-_]IN/i.test(v.lang)) || voices.find(v => /en[-_]GB/i.test(v.lang)) || voices.find(v => v.default) || voices[0];
      voiceSel.innerHTML = voices.map(v => `<option value="${esc(v.name)}"${pref && v.name === pref.name ? ' selected' : ''}>${esc(v.name)} (${esc(v.lang)})</option>`).join('') || '<option>Default voice</option>';
    }
    function speak(id) {
      cur = id; caption(id, -1);
      if (!synth) return;
      synth.cancel();
      const my = ++token, ss = sentences(script(id));
      playing = true; paused = false; setBtn();
      const v = voices.find(x => x.name === voiceSel.value);
      ss.forEach((s, k) => {
        const u = new window.SpeechSynthesisUtterance(s.trim());
        if (v) { u.voice = v; u.lang = v.lang; } else u.lang = 'en-IN';
        u.rate = +rateSel.value || 1;
        u.onstart = () => { if (my === token) caption(id, k); };
        if (k === ss.length - 1) u.onend = () => { if (my === token) { playing = false; paused = false; setBtn(); caption(id, -1); } };
        u.onerror = () => { if (my === token && k === ss.length - 1) { playing = false; setBtn(); } };
        synth.speak(u);
      });
    }
    function stop() { token++; if (synth) synth.cancel(); playing = false; paused = false; setBtn(); }
    function open(id) {
      panel.hidden = false; fab.setAttribute('aria-expanded', 'true');
      speak(id || inView);
    }
    function close() { stop(); panel.hidden = true; fab.setAttribute('aria-expanded', 'false'); }
    fab.addEventListener('click', () => (panel.hidden ? open() : close()));
    $('#vg-close').addEventListener('click', close);
    document.addEventListener('keydown', e => { if (e.key === 'Escape' && !panel.hidden) close(); });
    $('#vg-play').addEventListener('click', () => {
      if (!synth) return;
      if (!playing) speak(cur);
      else if (!paused) { synth.pause(); paused = true; setBtn(); }
      else { synth.resume(); paused = false; setBtn(); }
    });
    const go = d => { const ix = ORDER.indexOf(cur) + d; if (ix < 0 || ix >= ORDER.length) return; scrollToId(ORDER[ix]); speak(ORDER[ix]); };
    $('#vg-next').addEventListener('click', () => go(1));
    $('#vg-prev').addEventListener('click', () => go(-1));
    follow.addEventListener('change', () => store.set('vgFollow', follow.checked));
    rateSel.addEventListener('change', () => { store.set('vgRate', +rateSel.value); if (playing) speak(cur); });
    voiceSel.addEventListener('change', () => { store.set('vgVoice', voiceSel.value); if (playing) speak(cur); });
    document.addEventListener('click', e => { const b = e.target.closest('[data-listen]'); if (b) open(b.dataset.listen); });
    if (!synth) { $('#vg-na').hidden = false; $('#vg-play').disabled = true; $('#vg-voice-wrap').hidden = true; }
    else { loadVoices(); if ('onvoiceschanged' in synth) synth.onvoiceschanged = loadVoices; }
    if ('IntersectionObserver' in window) {
      const io = new IntersectionObserver(es => es.forEach(en => {
        if (!en.isIntersecting) return;
        const id = en.target.id;
        if (!GUIDE[id] || id === inView) return;
        inView = id;
        if (panel.hidden) return;
        if (follow.checked) { clearTimeout(followT); followT = setTimeout(() => { if (inView === id && cur !== id) speak(id); }, 700); }
        else if (!playing) { cur = id; caption(id, -1); }
      }), { rootMargin: '-40% 0px -55% 0px' });
      ORDER.forEach(id => { const el = document.getElementById(id); if (el) io.observe(el); });
    }
    caption('top', -1); setBtn();
  }

  /* ================================================================
     24. Completion card
     ================================================================ */
  function initCard() {
    const make = $('#cd-make'); if (!make) return;
    const main = $('main');
    const siteUrl = (main && main.dataset.siteUrl) || '';
    const nameIn = $('#cd-name');
    nameIn.value = store.get('cdName', '');
    let blob = null;
    const stats = () => ({
      ch: store.get('ch', []).length, bugs: store.get('bugs', []).length, dr: store.get('drill', []).length,
      pz: store.get('pz', []).length, qb: store.get('quizBest', 0)
    });
    async function draw(name) {
      const W = 1200, H = 627, cv = document.createElement('canvas'); cv.width = W; cv.height = H;
      const g = cv.getContext && cv.getContext('2d');
      if (!g) return null;
      try { if (document.fonts && document.fonts.ready) await document.fonts.ready; } catch (e) { /* fonts optional */ }
      const P = { bg: '#f1f2ee', ink: '#141b22', muted: '#58626c', accent: '#2b44c0', line: '#d3d7cf', ok: '#1d7a3c', card: '#ffffff', resp: '#b22c4d' };
      const S = stats(), complete = S.ch >= CHAPTERS.length;
      g.fillStyle = P.bg; g.fillRect(0, 0, W, H);
      g.fillStyle = P.accent; g.fillRect(0, 0, W, 10);
      // waveform motif: SETUP, one wait, triple-high edge
      const x0 = 700, cw = 64, rows = [['PSEL', [0, 1, 1, 1, 0, 0], P.accent], ['PENABLE', [0, 0, 1, 1, 0, 0], P.accent], ['PREADY', [0, 0, 0, 1, 0, 0], P.resp]];
      g.font = '600 15px "JetBrains Mono", ui-monospace, monospace';
      rows.forEach(([nm, vals, col], r) => {
        const yHi = 62 + r * 46, yLo = yHi + 24;
        g.fillStyle = P.muted; g.fillText(nm, x0 - 96, yLo - 4);
        g.strokeStyle = col; g.lineWidth = 3; g.beginPath();
        vals.forEach((v, i) => { const x = x0 + i * cw, y = v ? yHi : yLo; if (i === 0) g.moveTo(x, y); else g.lineTo(x, y); g.lineTo(x + cw, y); });
        g.stroke();
      });
      g.strokeStyle = P.ok; g.lineWidth = 2; g.setLineDash([5, 5]); g.beginPath(); g.moveTo(x0 + 4 * cw, 48); g.lineTo(x0 + 4 * cw, 200); g.stroke(); g.setLineDash([]);
      g.fillStyle = P.ok; g.font = '600 13px "JetBrains Mono", ui-monospace, monospace'; g.fillText('triple-high edge', x0 + 4 * cw + 8, 214);
      g.fillStyle = P.accent; g.font = '600 20px "JetBrains Mono", ui-monospace, monospace';
      g.fillText('POSEDGE · APB LAB', 70, 80);
      g.fillStyle = P.ink;
      let fs = 76; const nm = name || 'An APB learner';
      do { g.font = `800 ${fs}px "Archivo", "Arial Narrow", Arial, sans-serif`; fs -= 4; } while (g.measureText(nm).width > 1060 && fs > 30);
      g.fillText(nm, 70, 300);
      g.fillStyle = P.muted; g.font = '400 30px "IBM Plex Sans", system-ui, sans-serif';
      g.fillText(complete ? 'completed the APB protocol and verification track' : 'is working through the APB protocol and verification track', 70, 352);
      const boxes = [[`${S.ch}/${CHAPTERS.length}`, 'chapters'], [`${S.bugs}/${BUGS.length}`, 'bugs caught'], [`${S.dr}/${DRILLS.length}`, 'waveforms drawn'], [`${S.pz}/${PUZZLES.length}`, 'bug hunts'], [S.qb ? S.qb + '%' : '–', 'best quiz']];
      boxes.forEach(([big, lab], i) => {
        const x = 70 + i * 214, y = 400;
        g.fillStyle = P.card; g.strokeStyle = P.line; g.lineWidth = 2;
        g.beginPath(); if (g.roundRect) g.roundRect(x, y, 196, 118, 10); else g.rect(x, y, 196, 118); g.fill(); g.stroke();
        g.fillStyle = P.accent; g.font = '800 46px "Archivo", "Arial Narrow", Arial, sans-serif'; g.fillText(big, x + 20, y + 62);
        g.fillStyle = P.muted; g.font = '400 19px "IBM Plex Sans", system-ui, sans-serif'; g.fillText(lab, x + 20, y + 96);
      });
      g.fillStyle = P.muted; g.font = '400 18px "IBM Plex Sans", system-ui, sans-serif';
      g.fillText('Free interactive course · AMBA APB2 to APB5 · waveforms, SVA, constraints, coverage', 70, 576);
      g.textAlign = 'right';
      g.fillText(new Date().toLocaleDateString('en-GB', { day: 'numeric', month: 'long', year: 'numeric' }), W - 70, 576);
      g.textAlign = 'left';
      return cv;
    }
    make.addEventListener('click', async () => {
      const name = nameIn.value.trim().slice(0, 40);
      store.set('cdName', name);
      const cv = await draw(name);
      if (!cv) { $('#cd-note').textContent = 'This browser cannot draw the card.'; return; }
      const img = $('#cd-img');
      img.src = cv.toDataURL('image/png'); img.hidden = false;
      blob = await new Promise(r => cv.toBlob(r, 'image/png'));
      $('#cd-acts').hidden = false;
      const S = stats();
      $('#cd-note').textContent = S.ch >= CHAPTERS.length ? 'Your card says “completed”. Well done.' : `Your card says “working through” until all ${CHAPTERS.length} chapters are marked done.`;
    });
    $('#cd-save').addEventListener('click', async () => {
      if (!blob) return;
      const note = $('#cd-note');
      try {
        const dl = window.claude && typeof window.claude.use === 'function' ? await window.claude.use('downloads') : null;
        if (dl) { await dl.save({ filename: 'posedge-apb-card.png', data: blob }); note.textContent = 'Saved.'; return; }
      } catch (e) {
        if (e && e.code === 'declined') { note.textContent = 'Not saved. You can also right-click or long-press the card to save it.'; return; }
      }
      try {
        const u = URL.createObjectURL(blob), a = document.createElement('a');
        a.href = u; a.download = 'posedge-apb-card.png'; document.body.appendChild(a); a.click(); a.remove();
        setTimeout(() => URL.revokeObjectURL(u), 4000);
        note.textContent = 'If nothing downloaded, right-click or long-press the card to save it.';
      } catch (e) { note.textContent = 'Right-click or long-press the card to save it.'; }
    });
    $('#cd-post').addEventListener('click', e => {
      const S = stats();
      const t = `I've been learning the AMBA APB protocol with PosEdge, a free interactive lab: live waveforms, SystemVerilog assertions, constraints and coverage.\n\n` +
        `Progress: ${S.ch}/${CHAPTERS.length} chapters · ${S.bugs}/${BUGS.length} bugs caught · ${S.dr}/${DRILLS.length} waveforms drawn from memory${S.qb ? ` · quiz ${S.qb}%` : ''}\n\n` +
        (siteUrl ? `Try it: ${siteUrl}\n\n` : '') + '#VLSI #DesignVerification #SystemVerilog #AMBA #APB';
      copyText(t, e.currentTarget, null);
    });
  }

  /* ================================================================
     25. Chapter feedback
     ================================================================ */
  function initFeedback() {
    const main = $('main');
    const url = (main && main.dataset.feedbackUrl) || '';
    const votes = store.get('fb', {});
    const paint = (box, id) => {
      const v = votes[id];
      if (!v) return;
      box.innerHTML = `<span>${v === 'y' ? 'Glad it helped.' : 'Thanks for telling me.'}</span>` +
        (v === 'n' ? ` <button type="button" class="linkbtn" data-listen="${id}">Hear a short guide to this section</button>` : '') +
        (url ? ` <a href="${esc(url)}" target="_blank" rel="noopener">${v === 'n' ? 'Tell me what was unclear' : 'Suggest an improvement'}</a>` : '');
    };
    $$('.sec-end').forEach(end => {
      const id = end.closest('section').id;
      const box = document.createElement('div');
      box.className = 'fb';
      box.innerHTML = `<span>Was this chapter clear?</span><button type="button" class="btn sm" data-fb="y">Yes</button><button type="button" class="btn sm" data-fb="n">Not really</button>`;
      end.insertBefore(box, end.querySelector('.ch-done'));
      paint(box, id);
      box.addEventListener('click', e => {
        const b = e.target.closest('[data-fb]'); if (!b) return;
        votes[id] = b.dataset.fb; store.set('fb', votes); paint(box, id);
      });
    });
  }

  /* ================================================================
     21. SystemVerilog highlighting for code blocks
     ================================================================ */
  const SV_KW = new Set(('module endmodule interface endinterface input output inout logic wire reg bit byte int integer unsigned signed parameter localparam ' +
    'always always_ff always_comb assign if else begin end for foreach forever repeat do while case unique endcase default posedge negedge or and not ' +
    'property endproperty sequence endsequence assert assume cover restrict disable iff clocking endclocking class endclass extends function endfunction ' +
    'task endtask rand randc constraint dist inside solve before covergroup endgroup coverpoint cross bins ignore_bins illegal_bins option with ' +
    'typedef enum struct packed return virtual new null this super bind automatic static void string type_id create item index').split(' '));
  function hlSV(src) {
    const re = /(\/\/[^\n]*|\/\*[\s\S]*?\*\/)|("(?:[^"\\]|\\.)*")|(`\w+)|(\$\w+)|(\b\d*'[sS]?[bBhHdDoO][0-9a-fA-FxXzZ_]+|'[01xz]\b|\b\d+(?:\.\d+)?\b)|(\|->|\|=>|##\[[^\]]*\]|##\d+|\[\*\d*(?::\d+)?\])|([A-Za-z_]\w*)/g;
    let out = '', last = 0, m;
    while ((m = re.exec(src))) {
      out += esc(src.slice(last, m.index));
      const t = esc(m[0]);
      if (m[1]) out += `<span class="t-c">${t}</span>`;
      else if (m[2]) out += `<span class="t-s">${t}</span>`;
      else if (m[3]) out += `<span class="t-m">${t}</span>`;
      else if (m[4]) out += `<span class="t-f">${t}</span>`;
      else if (m[5]) out += `<span class="t-n">${t}</span>`;
      else if (m[6]) out += `<span class="t-o">${t}</span>`;
      else if (SV_KW.has(m[0])) out += `<span class="t-k">${t}</span>`;
      else if (/^P[A-Z]+[0-9]?n?$/.test(m[0])) out += `<span class="t-p">${t}</span>`;
      else out += t;
      last = re.lastIndex;
    }
    return out + esc(src.slice(last));
  }
  function initCode() {
    $$('script[type="text/x-sv"]').forEach(sc => {
      const src = sc.textContent.replace(/^\n+/, '').replace(/\s+$/, '');
      const fig = document.createElement('figure');
      fig.className = 'code';
      fig.innerHTML = `<figcaption><span>${esc(sc.dataset.title || 'SystemVerilog')}</span><button type="button" class="copy">Copy</button></figcaption><pre><code>${hlSV(src)}</code></pre>`;
      sc.replaceWith(fig);
      const btn = fig.querySelector('.copy');
      btn.addEventListener('click', () => {
        const done = t => { btn.textContent = t; setTimeout(() => { btn.textContent = 'Copy'; }, 1600); };
        const fallback = () => {
          const r = document.createRange(); r.selectNodeContents(fig.querySelector('code'));
          const sel = window.getSelection(); sel.removeAllRanges(); sel.addRange(r);
          done('Selected, press Ctrl+C');
        };
        try {
          if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(src).then(() => done('Copied'), fallback);
          else fallback();
        } catch (e) { fallback(); }
      });
    });
  }

  /* ================================================================
     Boot
     ================================================================ */
  function boot() {
    initCode();
    initChapters();
    initFeedback();
    initGuide();
    initHero();
    initSignals();
    initFSM();
    initCheckpoint();
    const lab = initLab();
    initVersions(lab);
    initRules();
    initPuzzles(lab);
    initExercises();
    initSite();
    initDeepLinks(lab);
    initDrill();
    initCard();
    initQuiz();
    initNav();
    progress();
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot); else boot();
})();
