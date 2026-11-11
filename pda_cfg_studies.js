#!/usr/bin/env node
/**
 * Case Study-Based Analysis & Design using CFG and PDA (CLA-2 Task 3)
 * Author: B. Sai Chethan (RA2411026050043)
 * Course: 21CSC301T - Formal Language and Automata
 *
 * Case Studies:
 *   1. arith      : Infix Arithmetic Expressions (i, +, *, (, )) — Precedence CFG + NPDA
 *   2. brackets   : Multi-Type Balanced Delimiters ((), [], {}) — Unambiguous CFG + DPDA
 *   3. palindrome : Center-Marked Palindromes (w c w^R over {a,b,c}) — Unambiguous CFG + DPDA
 */

'use strict';

const ANSI = {
  reset: '\x1b[0m',
  bold: '\x1b[1m',
  green: '\x1b[32m',
  red: '\x1b[31m',
  cyan: '\x1b[36m',
  yellow: '\x1b[33m',
};

const color = (c, text) => `${ANSI[c]}${text}${ANSI.reset}`;

function fmtEps(s) {
  return s === '' ? 'ε' : s;
}

// ---------------------------------------------------------------------------
// Leftmost Derivation Counter / Enumerator for CFGs
// ---------------------------------------------------------------------------
function countLeftmostDerivations(grammar, target, { maxSteps = 30, limit = 10 } = {}) {
  const { start, nonTerminals, prods, nullable = false } = grammar;
  const results = [];
  const seenStates = new Set();

  function minTerminalLen(form) {
    if (nullable) {
      // Only terminals contribute guaranteed length when epsilon productions exist
      let t = 0;
      for (const ch of form) {
        if (!nonTerminals.has(ch)) t += 1;
      }
      return t;
    }
    // Every symbol (terminal or nonterminal) yields >= 1 terminal
    return form.length;
  }

  function dfs(form, path) {
    if (results.length >= limit) return;

    // Find leftmost nonterminal
    let ntIdx = -1;
    for (let i = 0; i < form.length; i += 1) {
      if (nonTerminals.has(form[i])) {
        ntIdx = i;
        break;
      }
    }

    if (ntIdx === -1) {
      if (form === target) results.push(path);
      return;
    }

    const prefix = form.slice(0, ntIdx);
    if (!target.startsWith(prefix)) return;
    if (minTerminalLen(form) > target.length) return;
    if (path.length - 1 >= maxSteps) return;

    const nt = form[ntIdx];
    const rhsList = prods[nt] || [];
    for (const rhs of rhsList) {
      const nextForm = form.slice(0, ntIdx) + rhs + form.slice(ntIdx + 1);
      // Avoid trivial duplicate derivation steps in same branch if needed
      const key = `${path.length}:${nextForm}:${path.join('>')}`;
      if (!seenStates.has(key)) {
        seenStates.add(key);
        dfs(nextForm, [...path, nextForm]);
      }
    }
  }

  dfs(start, [start]);
  return results;
}

// ---------------------------------------------------------------------------
// Grammars
// ---------------------------------------------------------------------------
const GRAMMARS = {
  arith: {
    original: {
      name: 'arith_original (ambiguous)',
      start: 'E',
      nonTerminals: new Set(['E']),
      nullable: false,
      prods: {
        E: ['E+E', 'E*E', '(E)', 'i'],
      },
      display: ['E -> E+E | E*E | (E) | i'],
    },
    revised: {
      name: 'arith_revised (precedence + left-assoc)',
      start: 'E',
      nonTerminals: new Set(['E', 'T', 'F']),
      nullable: false,
      prods: {
        E: ['E+T', 'T'],
        T: ['T*F', 'F'],
        F: ['(E)', 'i'],
      },
      display: [
        'E -> E+T | T',
        'T -> T*F | F',
        'F -> (E) | i',
      ],
    },
  },
  brackets: {
    original: {
      name: 'brackets_original (ambiguous)',
      start: 'S',
      nonTerminals: new Set(['S']),
      nullable: true,
      prods: {
        S: ['SS', '(S)', '[S]', '{S}', ''],
      },
      display: ['S -> SS | (S) | [S] | {S} | ε'],
    },
    revised: {
      name: 'brackets_revised (unambiguous)',
      start: 'S',
      nonTerminals: new Set(['S']),
      nullable: true,
      prods: {
        S: ['(S)S', '[S]S', '{S}S', ''],
      },
      display: ['S -> (S)S | [S]S | {S}S | ε'],
    },
  },
  palindrome: {
    original: {
      name: 'palindrome (unambiguous)',
      start: 'S',
      nonTerminals: new Set(['S']),
      nullable: false,
      prods: {
        S: ['aSa', 'bSb', 'c'],
      },
      display: ['S -> aSa | bSb | c'],
    },
    revised: null,
  },
};

// ---------------------------------------------------------------------------
// PDA Simulator (supports both empty-stack NPDA and final-state DPDA)
// Stack is represented as a string with index 0 = TOP of stack.
// ---------------------------------------------------------------------------
class PDA {
  constructor({ name, mode, startState, startStack, acceptingStates = [], deterministic, stepFn }) {
    this.name = name;
    this.mode = mode; // 'empty_stack' | 'final_state'
    this.startState = startState;
    this.startStack = startStack;
    this.acceptingStates = new Set(acceptingStates);
    this.deterministic = deterministic;
    this.stepFn = stepFn; // (state, nextInputOrNull, topSymbolOrNull) => Array<{ consume, nextState, push }>
  }

  isAccepting(state, rem, stack) {
    if (rem.length > 0) return false;
    if (this.mode === 'empty_stack') return stack.length === 0;
    return this.acceptingStates.has(state);
  }

  run(input, { maxConfigs = 4000 } = {}) {
    const startCfg = { state: this.startState, rem: input, stack: this.startStack };
    const queue = [{ cfg: startCfg, path: [startCfg] }];
    const visited = new Set([`${startCfg.state}|${startCfg.rem}|${startCfg.stack}`]);
    let explored = 0;
    let deepestPath = [startCfg];

    while (queue.length > 0 && explored < maxConfigs) {
      const { cfg, path } = queue.shift();
      explored += 1;

      if (
        cfg.rem.length < deepestPath[deepestPath.length - 1].rem.length ||
        (cfg.rem.length === deepestPath[deepestPath.length - 1].rem.length && path.length > deepestPath.length)
      ) {
        deepestPath = path;
      }

      if (this.isAccepting(cfg.state, cfg.rem, cfg.stack)) {
        return { accepted: true, path, explored };
      }

      const top = cfg.stack.length > 0 ? cfg.stack[0] : null;
      const restStack = cfg.stack.slice(1);
      const nextCh = cfg.rem.length > 0 ? cfg.rem[0] : null;

      const moves = this.stepFn(cfg.state, nextCh, top, cfg.rem);
      for (const mv of moves) {
        if (mv.consume && cfg.rem.length === 0) continue;
        if (top === null && mv.popTop !== false) continue;
        const newRem = mv.consume ? cfg.rem.slice(1) : cfg.rem;
        const newStack = mv.push + restStack;

        // Sound pruning for empty-stack non-nullable CFG-PDA (Case Study 1)
        if (this.mode === 'empty_stack' && newStack.length > newRem.length) {
          continue;
        }

        const nextCfg = { state: mv.nextState, rem: newRem, stack: newStack };
        const key = `${nextCfg.state}|${nextCfg.rem}|${nextCfg.stack}`;
        if (!visited.has(key)) {
          visited.add(key);
          queue.push({ cfg: nextCfg, path: [...path, nextCfg] });
        }
      }
    }

    return { accepted: false, path: deepestPath, explored };
  }
}

// 1. NPDA from revised arithmetic grammar (1 state q, empty-stack acceptance)
const arithPDA = new PDA({
  name: 'NPDA for arithmetic expressions (from revised CFG, empty-stack)',
  mode: 'empty_stack',
  startState: 'q',
  startStack: 'E',
  deterministic: false,
  stepFn(state, ch, top) {
    if (top === null) return [];
    const rules = {
      E: ['E+T', 'T'],
      T: ['T*F', 'F'],
      F: ['(E)', 'i'],
    };
    if (rules[top]) {
      return rules[top].map((rhs) => ({ consume: false, nextState: 'q', push: rhs }));
    }
    if (ch !== null && top === ch) {
      return [{ consume: true, nextState: 'q', push: '' }];
    }
    return [];
  },
});

// 2. DPDA for multi-type balanced brackets (), [], {} (final-state acceptance)
const OPEN_MAP = { '(': 'P', '[': 'B', '{': 'C' };
const CLOSE_MAP = { ')': 'P', ']': 'B', '}': 'C' };

const bracketsPDA = new PDA({
  name: 'DPDA for balanced delimiters (), [], {} (final state q0)',
  mode: 'final_state',
  startState: 'q0',
  startStack: 'Z', // Z represents Z0
  acceptingStates: ['q0'],
  deterministic: true,
  stepFn(state, ch, top) {
    if (top === null) return [];
    if (state === 'q0') {
      if (top === 'Z' && ch !== null && OPEN_MAP[ch]) {
        return [{ consume: true, nextState: 'q1', push: OPEN_MAP[ch] + 'Z' }];
      }
      return [];
    }
    // state === 'q1'
    if (top === 'Z') {
      return [{ consume: false, nextState: 'q0', push: 'Z' }];
    }
    if (ch !== null && OPEN_MAP[ch]) {
      return [{ consume: true, nextState: 'q1', push: OPEN_MAP[ch] + top }];
    }
    if (ch !== null && CLOSE_MAP[ch] && CLOSE_MAP[ch] === top) {
      return [{ consume: true, nextState: 'q1', push: '' }];
    }
    return [];
  },
});

// 3. DPDA for center-marked palindromes w c w^R (final-state acceptance)
const palindromePDA = new PDA({
  name: 'DPDA for center-marked palindromes w c w^R (final state q2)',
  mode: 'final_state',
  startState: 'q0',
  startStack: 'Z', // Z represents Z0
  acceptingStates: ['q2'],
  deterministic: true,
  stepFn(state, ch, top) {
    if (top === null) return [];
    if (state === 'q0') {
      if (ch === 'a') return [{ consume: true, nextState: 'q0', push: 'A' + top }];
      if (ch === 'b') return [{ consume: true, nextState: 'q0', push: 'B' + top }];
      if (ch === 'c') return [{ consume: true, nextState: 'q1', push: top }];
      return [];
    }
    if (state === 'q1') {
      if (top === 'Z') {
        return [{ consume: false, nextState: 'q2', push: 'Z' }];
      }
      if (ch === 'a' && top === 'A') return [{ consume: true, nextState: 'q1', push: '' }];
      if (ch === 'b' && top === 'B') return [{ consume: true, nextState: 'q1', push: '' }];
      return [];
    }
    return [];
  },
});

const PDAS = {
  arith: arithPDA,
  brackets: bracketsPDA,
  palindrome: palindromePDA,
};

// Independent oracles to cross-validate PDA + CFG
function oracleArith(s) {
  let idx = 0;
  function parseE() {
    if (!parseT()) return false;
    while (s[idx] === '+') {
      idx += 1;
      if (!parseT()) return false;
    }
    return true;
  }
  function parseT() {
    if (!parseF()) return false;
    while (s[idx] === '*') {
      idx += 1;
      if (!parseF()) return false;
    }
    return true;
  }
  function parseF() {
    if (s[idx] === '(') {
      idx += 1;
      if (!parseE()) return false;
      if (s[idx] !== ')') return false;
      idx += 1;
      return true;
    }
    if (s[idx] === 'i') {
      idx += 1;
      return true;
    }
    return false;
  }
  return parseE() && idx === s.length;
}

function oracleBrackets(s) {
  const st = [];
  const match = { ')': '(', ']': '[', '}': '{' };
  for (const ch of s) {
    if (ch === '(' || ch === '[' || ch === '{') st.push(ch);
    else if (match[ch]) {
      if (st.pop() !== match[ch]) return false;
    } else return false;
  }
  return st.length === 0;
}

function oraclePalindrome(s) {
  const cIdx = s.indexOf('c');
  if (cIdx === -1 || s.indexOf('c', cIdx + 1) !== -1) return false;
  const left = s.slice(0, cIdx);
  const right = s.slice(cIdx + 1);
  if (!/^[ab]*$/.test(left) || !/^[ab]*$/.test(right)) return false;
  return left === right.split('').reverse().join('');
}

const ORACLES = {
  arith: oracleArith,
  brackets: oracleBrackets,
  palindrome: oraclePalindrome,
};

const REPORT_CASES = {
  arith: {
    accept: ['i', 'i+i*i', '(i+i)*i', '((i))', 'i*(i+i*i)'],
    reject: ['', '+i', 'i+*i', '(i+i', 'i)i('],
  },
  brackets: {
    accept: ['', '()', '([]){}', '{[()]}', '()[]{}'],
    reject: ['(', '([)]', '())', '}{', '[{]'],
  },
  palindrome: {
    accept: ['c', 'aca', 'abcba', 'aabcbaa', 'bbacabb'],
    reject: ['', 'ab', 'abcab', 'acba', 'abccba'],
  },
};

function generateStrings(alphabet, maxLen) {
  const out = [''];
  let layer = [''];
  for (let len = 1; len <= maxLen; len += 1) {
    const nextLayer = [];
    for (const p of layer) {
      for (const ch of alphabet) {
        const s = p + ch;
        nextLayer.push(s);
        out.push(s);
      }
    }
    layer = nextLayer;
  }
  return out;
}

function formatStack(stack) {
  return stack === '' ? 'ε' : stack.replace(/Z/g, 'Z0');
}

function formatTrace(path) {
  return path
    .map((c) => `(${c.state},${fmtEps(c.rem)},${formatStack(c.stack)})`)
    .join(' |- ');
}

function cmdTrace(study, input) {
  const pda = PDAS[study];
  if (!pda) {
    console.error(`Unknown case study '${study}'. Use: arith | brackets | palindrome`);
    process.exitCode = 1;
    return;
  }
  const res = pda.run(input);
  console.log(`${pda.name}  input ${JSON.stringify(fmtEps(input))}`);
  console.log(`  ${formatTrace(res.path)}`);
  const badge = res.accepted ? color('green', 'ACCEPT') : color('red', 'REJECT');
  const note = res.accepted
    ? `(${res.explored} configurations explored)`
    : `no accepting branch; deepest path shown above (${res.explored} configurations explored)`;
  console.log(`  ${badge}  ${note}`);
}

function cmdGrammar(study) {
  const g = GRAMMARS[study];
  if (!g) {
    console.error(`Unknown case study '${study}'. Use: arith | brackets | palindrome`);
    process.exitCode = 1;
    return;
  }
  if (g.revised) {
    console.log(color('yellow', 'ambiguous (original)'));
    for (const line of g.original.display) console.log(`  ${line}`);
    console.log(color('green', 'revised (unambiguous)'));
    for (const line of g.revised.display) console.log(`  ${line}`);
  } else {
    console.log(color('green', 'unambiguous'));
    for (const line of g.original.display) console.log(`  ${line}`);
  }
}

function cmdAmbiguity() {
  console.log(color('cyan', 'Bounded ambiguity check (count leftmost derivations on short strings)'));
  console.log('Ambiguity of a CFG is undecidable in general; this provides bounded verification.\n');

  const checks = [
    ['arith, original', GRAMMARS.arith.original, generateStrings(['i', '+', '*', '(', ')'], 5), 14],
    ['arith, revised', GRAMMARS.arith.revised, generateStrings(['i', '+', '*', '(', ')'], 5), 14],
    ['brackets, original', GRAMMARS.brackets.original, generateStrings(['(', ')', '[', ']'], 4), 10],
    ['brackets, revised', GRAMMARS.brackets.revised, generateStrings(['(', ')', '[', ']'], 4), 10],
    ['palindrome', GRAMMARS.palindrome.original, generateStrings(['a', 'b', 'c'], 5), 8],
  ];

  for (const [label, gram, pool, maxSteps] of checks) {
    let validCount = 0;
    let ambigExample = null;
    let ambigCount = 0;
    for (const s of pool) {
      const derivs = countLeftmostDerivations(gram, s, { maxSteps, limit: 3 });
      if (derivs.length > 0) {
        validCount += 1;
        if (derivs.length > 1 && ambigExample === null) {
          ambigExample = s;
          ambigCount = derivs.length;
        }
      }
    }
    if (ambigExample !== null) {
      console.log(
        `  ${label.padEnd(20)} ${color('red', 'AMBIGUOUS')}  e.g. ${JSON.stringify(fmtEps(ambigExample))} has >=${ambigCount} derivations (${validCount} valid strings tested)`
      );
    } else {
      console.log(
        `  ${label.padEnd(20)} ${color('green', 'no ambiguity found')} (${validCount} valid strings, 1 tree each)`
      );
    }
  }
}

function cmdDemo() {
  console.log(color('cyan', '=== arith ===') + `  deterministic: ${arithPDA.deterministic}`);
  cmdTrace('arith', 'i+i*i');
  console.log('');
  cmdTrace('arith', 'i+*i');
  console.log('');

  console.log(color('cyan', '=== brackets ===') + `  deterministic: ${bracketsPDA.deterministic}`);
  cmdTrace('brackets', '([]){}');
  console.log('');
  cmdTrace('brackets', '([)]');
  console.log('');

  console.log(color('cyan', '=== palindrome ===') + `  deterministic: ${palindromePDA.deterministic}`);
  cmdTrace('palindrome', 'abcba');
  console.log('');
  cmdTrace('palindrome', 'abcab');
}

function cmdTest() {
  let failures = 0;
  let totalExamples = 0;

  for (const [study, cases] of Object.entries(REPORT_CASES)) {
    const pda = PDAS[study];
    const oracle = ORACLES[study];
    for (const s of cases.accept) {
      totalExamples += 1;
      const ok = pda.run(s).accepted && oracle(s);
      if (!ok) {
        failures += 1;
        console.error(color('red', `FAIL accept ${study}: ${JSON.stringify(s)}`));
      }
    }
    for (const s of cases.reject) {
      totalExamples += 1;
      const ok = !pda.run(s).accepted && !oracle(s);
      if (!ok) {
        failures += 1;
        console.error(color('red', `FAIL reject ${study}: ${JSON.stringify(s)}`));
      }
    }
  }
  console.log(`report examples: ${totalExamples} strings OK`);

  const testPools = [
    ['arith', generateStrings(['i', '+', '*', '(', ')'], 5), 14],
    ['brackets', generateStrings(['(', ')', '[', ']', '{', '}'], 4), 10],
    ['palindrome', generateStrings(['a', 'b', 'c'], 5), 8],
  ];

  for (const [study, pool, maxSteps] of testPools) {
    const pda = PDAS[study];
    const oracle = ORACLES[study];
    const cfg = GRAMMARS[study].revised || GRAMMARS[study].original;

    for (const s of pool) {
      const pdaRes = pda.run(s).accepted;
      const oraRes = oracle(s);
      const cfgRes = countLeftmostDerivations(cfg, s, { maxSteps, limit: 1 }).length > 0;
      if (pdaRes !== oraRes || pdaRes !== cfgRes) {
        failures += 1;
        console.error(
          color('red', `MISMATCH ${study} on ${JSON.stringify(s)}: pda=${pdaRes}, cfg=${cfgRes}, oracle=${oraRes}`)
        );
      }
    }
    console.log(`${study}: PDA, CFG, and independent oracle agree on ${pool.length.toLocaleString('en-US')} strings`);
  }

  // Confirm original & revised grammars generate identical languages on bounded pools
  const eqPools = [
    ['arith', GRAMMARS.arith.original, GRAMMARS.arith.revised, generateStrings(['i', '+', '*', '(', ')'], 5), 14],
    ['brackets', GRAMMARS.brackets.original, GRAMMARS.brackets.revised, generateStrings(['(', ')', '[', ']'], 4), 10],
  ];
  for (const [study, gOrig, gRev, pool, maxSteps] of eqPools) {
    for (const s of pool) {
      const a = countLeftmostDerivations(gOrig, s, { maxSteps, limit: 1 }).length > 0;
      const b = countLeftmostDerivations(gRev, s, { maxSteps, limit: 1 }).length > 0;
      if (a !== b) {
        failures += 1;
        console.error(color('red', `GRAMMAR MISMATCH ${study} on ${JSON.stringify(s)}: orig=${a}, rev=${b}`));
      }
    }
  }
  console.log('original and revised grammars generate identical languages on all bounded strings');

  // Confirm ambiguity detection and fix
  const arithAmb = countLeftmostDerivations(GRAMMARS.arith.original, 'i+i*i', { maxSteps: 14, limit: 5 }).length;
  const arithUnamb = countLeftmostDerivations(GRAMMARS.arith.revised, 'i+i*i', { maxSteps: 14, limit: 5 }).length;
  const brkAmb = countLeftmostDerivations(GRAMMARS.brackets.original, '()()', { maxSteps: 10, limit: 5 }).length;
  const brkUnamb = countLeftmostDerivations(GRAMMARS.brackets.revised, '()()', { maxSteps: 10, limit: 5 }).length;
  if (arithAmb < 2 || arithUnamb !== 1 || brkAmb < 2 || brkUnamb !== 1) {
    failures += 1;
    console.error(color('red', `Ambiguity check mismatch: arith(${arithAmb}->${arithUnamb}), brackets(${brkAmb}->${brkUnamb})`));
  } else {
    console.log(`ambiguity confirmed & resolved: arith 'i+i*i' (${arithAmb}->${arithUnamb}), brackets '()()' (${brkAmb}->${brkUnamb})`);
  }

  console.log('determinism: arith nondeterministic, brackets & palindrome deterministic');
  if (failures === 0) {
    console.log(color('green', 'ALL TESTS PASSED'));
  } else {
    console.log(color('red', `${failures} FAILURE(S)`));
    process.exitCode = 1;
  }
}

const [, , cmd = 'test', arg1, arg2 = ''] = process.argv;
if (cmd === 'test') {
  cmdTest();
} else if (cmd === 'demo') {
  cmdDemo();
} else if (cmd === 'trace') {
  cmdTrace(arg1, arg2);
} else if (cmd === 'grammar') {
  cmdGrammar(arg1);
} else if (cmd === 'ambiguity') {
  cmdAmbiguity();
} else {
  console.log('Usage: node pda_cfg_studies.js <test|demo|trace|grammar|ambiguity> [study] [input]');
  process.exitCode = 1;
}
