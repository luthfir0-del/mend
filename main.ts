// mend — one patch tool for every AI edit format.
//
// Node 22, the standard library alone. SPEC.md is the contract; this file
// implements all of it: the command line (section 1), the output and exit
// codes (section 2), safe paths and file lines (section 3), format
// detection (section 4), three-tier line matching (section 5), unified
// diffs (section 6), SEARCH/REPLACE blocks (section 7), V4A patches
// (section 8), JSON edits (section 9), and the all-or-nothing write
// (section 10). Run as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set,
// and this file hands over to runner.ts (the last lines below).

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** An exit-2 outcome: the whole run stops with one line on stdout. */
class HardExit {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

/** One edit's failure: its code and the path it concerns. */
class EditFail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

/** A patch's lines (SPEC.md section 3): split at \n, one trailing \r off each, no empty piece after a final \n. */
function patchParts(text: string): string[] {
  if (text === '') return [];
  const parts = text.split('\n');
  if (text.endsWith('\n')) parts.pop();
  return parts.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** A path is safe when it is not empty, does not start with /, holds no \, and no segment is empty, . or .. . */
function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

interface FileParts {
  lines: string[];
  br: string;
  final: boolean;
}

/** A file's lines (SPEC.md section 3): its break is CRLF when its first line feed follows a carriage return, else LF. */
function fileParts(text: string): FileParts {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const final = text.endsWith(br);
  const lines = text.split(br);
  if (final) lines.pop();
  return { lines, br, final };
}

/** Join lines back with the file's own break; a file of no lines is written empty. */
function joinParts(lines: string[], br: string, final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (final ? br : '');
}

/** The leading spaces and tabs of a line. */
function leadingWs(s: string): string {
  const m = s.match(/^[ \t]*/);
  return m === null ? '' : m[0];
}

/** A line as a tier reads it: tier 0 exact, tier 1 trailing whitespace off, tier 2 both ends off. */
function norm(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** The tree the patch works on: what is on disk, plus what the edits so far have left it as. */
class Tree {
  private orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: { from: string; to: string }[] = [];

  /** A file's text, or null when it does not exist (reading the original from disk once, then reusing it). */
  original(p: string): string | null {
    if (this.orig.has(p)) return this.orig.get(p) as string | null;
    let t: string | null = null;
    try {
      if (statSync(p).isFile()) t = readFileSync(p, 'utf8');
    } catch {
      t = null;
    }
    this.orig.set(p, t);
    return t;
  }

  /** A file's text as the edits so far leave it, or null when it is absent. */
  get(p: string): string | null {
    if (this.now.has(p)) return this.now.get(p) as string | null;
    return this.original(p);
  }

  /** Replace the working map wholesale (an edit that fails restores the tree as it was before it). */
  restore(snapshot: Map<string, string | null>): void {
    this.now.clear();
    for (const [k, v] of snapshot) this.now.set(k, v);
  }
}

type Edit = (tree: Tree) => void;

interface BodyItem {
  k: 'c' | 'd' | 'a';
  t: string;
  noEol: boolean;
}

/** A body's old lines and, in order, the lines it writes (context lines carry the index of their old line). */
function splitBody(items: BodyItem[]): { o: string[]; n: { ctx: boolean; o: number; text: string }[] } {
  const o: string[] = [];
  const n: { ctx: boolean; o: number; text: string }[] = [];
  for (const it of items) {
    if (it.k === 'c') {
      n.push({ ctx: true, o: o.length, text: '' });
      o.push(it.t);
    } else if (it.k === 'd') {
      o.push(it.t);
    } else {
      n.push({ ctx: false, o: -1, text: it.t });
    }
  }
  return { o, n };
}

/** The lines a replacement writes (SPEC.md section 5): a context line is the file's own matched line; at tier 2 the other lines are re-indented under the file's first matched line. */
function buildReplacement(fileLines: string[], pos: number, o: string[], n: { ctx: boolean; o: number; text: string }[], tier: number): string[] {
  const out: string[] = [];
  let p = '';
  let f = '';
  if (tier === 2 && o.length > 0) {
    p = leadingWs(o[0] as string);
    f = leadingWs(fileLines[pos] as string);
  }
  for (const e of n) {
    if (e.ctx) {
      out.push(fileLines[pos + e.o] as string);
      continue;
    }
    let line = e.text;
    if (tier === 2 && line !== '' && line.trim() !== '' && line.startsWith(p)) line = f + line.slice(p.length);
    out.push(line);
  }
  return out;
}

/** Every 0-based position at which `oldLines` occurs in `fileLines` at this tier, from `from` on (an end-anchored search takes only occurrences that end on the file's last line). */
function occurrences(fileLines: string[], oldLines: string[], tier: number, from: number, endAnchored: boolean): number[] {
  const found: number[] = [];
  const n = oldLines.length;
  if (n === 0) return found;
  const old = oldLines.map((l) => norm(l, tier));
  for (let i = from; i + n <= fileLines.length; i++) {
    let ok = true;
    for (let k = 0; k < n; k++) {
      if (norm(fileLines[i + k] as string, tier) !== old[k]) {
        ok = false;
        break;
      }
    }
    if (ok && (!endAnchored || i + n === fileLines.length)) found.push(i);
  }
  return found;
}

/** Which format the patch text is, or null when none of the four fits. */
function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object, or null when the value is not a well-formed edit. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  if (typeof o.path !== 'string') return null;
  const p = o.path as string;
  if (o.command === 'create') {
    if (typeof o.file_text !== 'string') return null;
    const text = o.file_text as string;
    return (tree) => {
      if (!safe(p)) throw new EditFail('unsafe', p);
      if (tree.get(p) !== null) throw new EditFail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace') {
    if (typeof o.old_str !== 'string' || (o.old_str as string) === '') return null;
    if (o.new_str !== undefined && typeof o.new_str !== 'string') return null;
    const oldStr = o.old_str as string;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      if (!safe(p)) throw new EditFail('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new EditFail('missing', p);
      const crlf = fileParts(before).br === '\r\n';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      const nw = lf(newStr);
      let count = 0;
      let at = -1;
      for (let k = t.indexOf(old); k !== -1; k = t.indexOf(old, k + 1)) {
        if (count === 0) at = k;
        count++;
      }
      if (count === 0) throw new EditFail('no-match', p);
      if (count > 1) throw new EditFail('ambiguous', p);
      const out = t.slice(0, at) + nw + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert') {
    if (typeof o.insert_line !== 'number' || !Number.isInteger(o.insert_line as number)) return null;
    if (typeof o.new_str !== 'string') return null;
    const line = o.insert_line as number;
    const newStr = o.new_str as string;
    return (tree) => {
      if (!safe(p)) throw new EditFail('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new EditFail('missing', p);
      const parts = fileParts(before);
      if (line < 0 || line > parts.lines.length) throw new EditFail('no-match', p);
      const add = patchParts(newStr);
      const lines = parts.lines.slice();
      lines.splice(line, 0, ...add);
      tree.now.set(p, joinParts(lines, parts.br, parts.final));
    };
  }
  return null;
}

/** JSON (SPEC.md section 9): one JSON array of edits, or JSON Lines; a fault names the line it sits on. */
function parseJson(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new HardExit('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let parsed: unknown;
    try {
      parsed = JSON.parse(text);
    } catch {
      throw new HardExit(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(parsed)) throw new HardExit(`error: parse ${first + 1}`);
    for (const v of parsed) {
      const edit = jsonEdit(v);
      if (edit === null) throw new HardExit(`error: parse ${first + 1}`);
      edits.push(edit);
    }
    return edits;
  }
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i] as string;
    if (blank(line)) continue;
    let parsed: unknown;
    try {
      parsed = JSON.parse(line);
    } catch {
      throw new HardExit(`error: parse ${i + 1}`);
    }
    const edit = jsonEdit(parsed);
    if (edit === null) throw new HardExit(`error: parse ${i + 1}`);
    edits.push(edit);
  }
  return edits;
}

interface Hunk {
  a: number;
  body: BodyItem[];
}

interface Section {
  pairOld: string | null;
  pairNew: string | null;
  hasPair: boolean;
  renameOld: string | null;
  renameNew: string | null;
  diffOld: string | null;
  diffNew: string | null;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
}

/** A `--- <path>` or `+++ <path>` line's path: the text after four characters, up to the first tab, spaces trimmed; /dev/null means no file; a leading a/ or b/ is removed. */
function headerPath(line: string): string | null {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  if (p === '/dev/null') return null;
  return p;
}

/** The last context or `+` line of a hunk's body, or null when it has neither. */
function lastCtxOrAdd(body: BodyItem[]): BodyItem | null {
  for (let i = body.length - 1; i >= 0; i--) {
    const it = body[i] as BodyItem;
    if (it.k === 'c' || it.k === 'a') return it;
  }
  return null;
}

/** Apply a section's hunks, in order, to a file's text (SPEC.md section 6). */
function applyHunks(before: string, hunks: Hunk[], strict: boolean, path: string): string {
  const parts = fileParts(before);
  let lines = parts.lines.slice();
  let final = parts.final;
  const br = parts.br;
  let d = 0;
  for (const hunk of hunks) {
    const { o, n } = splitBody(hunk.body);
    if (o.length === 0) {
      let at = hunk.a + d;
      if (at < 0) at = 0;
      if (at > lines.length) at = lines.length;
      const runsToEnd = at === lines.length;
      const ins = n.map((e) => e.text);
      lines.splice(at, 0, ...ins);
      if (runsToEnd) {
        const last = lastCtxOrAdd(hunk.body);
        final = last === null ? true : !last.noEol;
      }
      d += n.length;
      continue;
    }
    let tier = -1;
    let occ: number[] = [];
    for (let t = 0; t <= 2; t++) {
      if (strict && t > 0) break;
      const found = occurrences(lines, o, t, 0, false);
      if (found.length > 0) {
        tier = t;
        occ = found;
        break;
      }
    }
    if (tier < 0) throw new EditFail('no-match', path);
    const target = hunk.a - 1 + d;
    let pos = occ[0] as number;
    for (const q of occ) {
      if (Math.abs(q - target) < Math.abs(pos - target)) pos = q;
    }
    const runsToEnd = pos + o.length === lines.length;
    const replacement = buildReplacement(lines, pos, o, n, tier);
    lines.splice(pos, o.length, ...replacement);
    if (runsToEnd) {
      const last = lastCtxOrAdd(hunk.body);
      final = last === null ? true : !last.noEol;
    }
    d += n.length - o.length;
  }
  return joinParts(lines, br, final);
}

/** One unified section as one edit (SPEC.md section 6). */
function sectionEdit(sec: Section, strict: boolean): Edit {
  let oldPath: string | null;
  let newPath: string | null;
  if (sec.hasPair) {
    oldPath = sec.pairOld;
    newPath = sec.pairNew;
  } else {
    oldPath = sec.renameOld ?? sec.diffOld;
    newPath = sec.renameNew ?? sec.diffNew;
  }
  if (oldPath === null || sec.newFile) {
    const np = newPath;
    return (tree) => {
      if (np === null) return;
      if (!safe(np)) throw new EditFail('unsafe', np);
      if (tree.get(np) !== null) throw new EditFail('exists', np);
      const plus: string[] = [];
      let lastNoEol = false;
      for (const hunk of sec.hunks) {
        for (const item of hunk.body) {
          if (item.k === 'a') {
            plus.push(item.t);
            lastNoEol = item.noEol;
          }
        }
      }
      tree.now.set(np, plus.length === 0 ? '' : plus.join('\n') + (lastNoEol ? '' : '\n'));
    };
  }
  if (newPath === null || sec.deletedFile) {
    const op = oldPath;
    return (tree) => {
      if (!safe(op)) throw new EditFail('unsafe', op);
      if (tree.get(op) === null) throw new EditFail('missing', op);
      tree.now.set(op, null);
    };
  }
  if (oldPath !== newPath) {
    const op = oldPath;
    const np = newPath;
    return (tree) => {
      if (!safe(op)) throw new EditFail('unsafe', op);
      if (!safe(np)) throw new EditFail('unsafe', np);
      const before = tree.get(op);
      if (before === null) throw new EditFail('missing', op);
      if (tree.get(np) !== null) throw new EditFail('exists', np);
      const out = applyHunks(before, sec.hunks, strict, op);
      tree.now.set(np, out);
      tree.now.set(op, null);
      tree.moves.push({ from: op, to: np });
    };
  }
  const p = oldPath;
  return (tree) => {
    if (!safe(p)) throw new EditFail('unsafe', p);
    const before = tree.get(p);
    if (before === null) throw new EditFail('missing', p);
    tree.now.set(p, applyHunks(before, sec.hunks, strict, p));
  };
}

/** Unified diffs (SPEC.md section 6): sections, headers, hunks, bodies. */
function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let hunk: Hunk | null = null;
  const isPlusPlus = (idx: number): boolean => idx < lines.length && (lines[idx] as string).startsWith('+++ ');
  const startSection = (diffOld: string | null, diffNew: string | null): void => {
    if (hunk !== null) finishHunk();
    cur = {
      pairOld: null,
      pairNew: null,
      hasPair: false,
      renameOld: null,
      renameNew: null,
      diffOld,
      diffNew,
      newFile: false,
      deletedFile: false,
      hunks: [],
    };
    sections.push(cur);
  };
  const finishHunk = (): void => {
    if (hunk === null || cur === null) return;
    while (hunk.body.length > 0) {
      const last = hunk.body[hunk.body.length - 1] as BodyItem;
      if (last.k === 'c' && last.t === '' && !last.noEol) hunk.body.pop();
      else break;
    }
    cur.hunks.push(hunk);
    hunk = null;
  };
  let i = 0;
  while (i < lines.length) {
    const line = lines[i] as string;
    if (hunk !== null) {
      if (line.startsWith('diff --git ')) {
        finishHunk();
        continue;
      }
      if (line.startsWith('--- ') && isPlusPlus(i + 1)) {
        finishHunk();
        continue;
      }
      if (line.startsWith(' ') || line.startsWith('-') || line.startsWith('+')) {
        hunk.body.push({ k: line[0] === ' ' ? 'c' : line[0] === '-' ? 'd' : 'a', t: line.slice(1), noEol: false });
        i++;
        continue;
      }
      if (line.startsWith('\\')) {
        const last = hunk.body[hunk.body.length - 1];
        if (last !== undefined) last.noEol = true;
        i++;
        continue;
      }
      if (line === '') {
        hunk.body.push({ k: 'c', t: '', noEol: false });
        i++;
        continue;
      }
      finishHunk();
      continue;
    }
    if (line.startsWith('diff --git ')) {
      const m = line.match(/^diff --git a\/(.+) b\/(.+)$/);
      if (m === null) throw new HardExit(`error: parse ${i + 1}`);
      startSection((m[1] as string).trim(), (m[2] as string).trim());
      i++;
      continue;
    }
    if (line.startsWith('--- ') && isPlusPlus(i + 1)) {
      if (cur !== null && cur.hunks.length === 0 && !cur.hasPair) {
        cur.pairOld = headerPath(line);
        cur.pairNew = headerPath(lines[i + 1] as string);
        cur.hasPair = true;
        i += 2;
        continue;
      }
      startSection(null, null);
      (cur as Section).pairOld = headerPath(line);
      (cur as Section).pairNew = headerPath(lines[i + 1] as string);
      (cur as Section).hasPair = true;
      i += 2;
      continue;
    }
    if (cur === null) {
      if (line.startsWith('@@')) throw new HardExit(`error: parse ${i + 1}`);
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      const m = line.match(/^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/);
      if (m === null) throw new HardExit(`error: parse ${i + 1}`);
      hunk = { a: Number(m[1]), body: [] };
      i++;
      continue;
    }
    if (cur.hunks.length === 0) {
      if (line.startsWith('--- ')) throw new HardExit(`error: parse ${i + 2}`);
      if (line.startsWith('rename from ')) {
        cur.renameOld = line.slice('rename from '.length).trim();
        i++;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renameNew = line.slice('rename to '.length).trim();
        i++;
        continue;
      }
      if (line.startsWith('new file mode')) {
        cur.newFile = true;
        i++;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        cur.deletedFile = true;
        i++;
        continue;
      }
      i++;
      continue;
    }
    i++;
  }
  if (hunk !== null) finishHunk();
  return sections.map((sec) => sectionEdit(sec, strict));
}

/** SEARCH/REPLACE (SPEC.md section 7): a path line, `<<<<<<< SEARCH`, old lines, `=======`, new lines, `>>>>>>> REPLACE`. */
function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if ((lines[i] as string).trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLine = i;
    let path: string | null = null;
    for (let j = searchLine - 1; j >= prevEnd; j--) {
      const l = lines[j] as string;
      if (blank(l)) continue;
      const t = l.trim();
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new HardExit(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = searchLine + 1; j < lines.length; j++) {
      const t = (lines[j] as string).trimEnd();
      if (t === '=======') {
        eq = j;
        break;
      }
      if (t === '<<<<<<< SEARCH' || t === '>>>>>>> REPLACE') break;
    }
    if (eq < 0) throw new HardExit(`error: parse ${searchLine + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      const t = (lines[j] as string).trimEnd();
      if (t === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
      if (t === '<<<<<<< SEARCH') break;
    }
    if (rep < 0) throw new HardExit(`error: parse ${searchLine + 1}`);
    const oldLines = lines.slice(searchLine + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    const p = path;
    edits.push((tree) => {
      if (!safe(p)) throw new EditFail('unsafe', p);
      if (oldLines.length === 0) {
        if (tree.get(p) !== null) throw new EditFail('exists', p);
        tree.now.set(p, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
        return;
      }
      const before = tree.get(p);
      if (before === null) throw new EditFail('missing', p);
      const parts = fileParts(before);
      let tier = -1;
      let occ: number[] = [];
      for (let t = 0; t <= 2; t++) {
        if (strict && t > 0) break;
        const found = occurrences(parts.lines, oldLines, t, 0, false);
        if (found.length > 0) {
          tier = t;
          occ = found;
          break;
        }
      }
      if (tier < 0) throw new EditFail('no-match', p);
      if (occ.length > 1) throw new EditFail('ambiguous', p);
      const pos = occ[0] as number;
      const n = newLines.map((text) => ({ ctx: false, o: -1, text }));
      const replacement = buildReplacement(parts.lines, pos, oldLines, n, tier);
      const out = parts.lines.slice();
      out.splice(pos, oldLines.length, ...replacement);
      tree.now.set(p, joinParts(out, parts.br, parts.final));
    });
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return edits;
}

interface V4aChunk {
  anchor: string | null;
  items: BodyItem[];
  eof: boolean;
}

function parseV4aUpdateBody(sec: { text: string; num: number }[], updateLine: number): { moveTo: string | null; chunks: V4aChunk[] } {
  let moveTo: string | null = null;
  const chunks: V4aChunk[] = [];
  let idx = 0;
  if (idx < sec.length && (sec[idx] as { text: string }).text.startsWith('*** Move to: ')) {
    moveTo = (sec[idx] as { text: string }).text.slice('*** Move to: '.length).trim();
    idx++;
  }
  let cur: V4aChunk | null = null;
  let chunkStarted = false;
  while (idx < sec.length) {
    const s = sec[idx] as { text: string; num: number };
    const l = s.text;
    if (l.startsWith('@@')) {
      if (cur !== null) chunks.push(cur);
      const a = l.slice(2).trim();
      cur = { anchor: a === '' ? null : a, items: [], eof: false };
      chunkStarted = true;
      idx++;
      continue;
    }
    if (l.trimEnd() === '*** End of File') {
      if (cur === null) throw new HardExit(`error: parse ${s.num}`);
      cur.eof = true;
      chunks.push(cur);
      cur = null;
      idx++;
      continue;
    }
    if (l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l === '') {
      if (cur === null) {
        if (chunkStarted) throw new HardExit(`error: parse ${s.num}`);
        cur = { anchor: null, items: [], eof: false };
        chunkStarted = true;
      }
      cur.items.push({ k: l === '' || l[0] === ' ' ? 'c' : l[0] === '-' ? 'd' : 'a', t: l === '' ? '' : l.slice(1), noEol: false });
      idx++;
      continue;
    }
    throw new HardExit(`error: parse ${s.num}`);
  }
  if (cur !== null) chunks.push(cur);
  if (chunks.length === 0 && moveTo === null) throw new HardExit(`error: parse ${updateLine}`);
  return { moveTo, chunks };
}

/** V4A (SPEC.md section 8): `*** Begin Patch` ... sections ... `*** End Patch`. */
function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new HardExit('error: parse 1');
  if ((lines[first] as string).trim() !== '*** Begin Patch') throw new HardExit(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i] as string)) {
      last = i;
      break;
    }
  }
  if ((lines[last] as string).trim() !== '*** End Patch') throw new HardExit(`error: parse ${lines.length + 1}`);
  const isSectionStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i] as string;
    if (blank(line)) {
      i++;
      continue;
    }
    if (line.startsWith('*** Add File: ')) {
      const path = line.slice('*** Add File: '.length).trim();
      const sec: { text: string; num: number }[] = [];
      let j = i + 1;
      while (j < last && !isSectionStart(lines[j] as string)) {
        sec.push({ text: lines[j] as string, num: j + 1 });
        j++;
      }
      while (sec.length > 0 && blank((sec[sec.length - 1] as { text: string }).text)) sec.pop();
      const fileLines: string[] = [];
      for (const s of sec) {
        if (s.text === '') fileLines.push('');
        else if (s.text.startsWith('+')) fileLines.push(s.text.slice(1));
        else throw new HardExit(`error: parse ${s.num}`);
      }
      edits.push((tree) => {
        if (!safe(path)) throw new EditFail('unsafe', path);
        if (tree.get(path) !== null) throw new EditFail('exists', path);
        tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
      i = j;
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const path = line.slice('*** Delete File: '.length).trim();
      let j = i + 1;
      while (j < last && !isSectionStart(lines[j] as string)) {
        if (!blank(lines[j] as string)) throw new HardExit(`error: parse ${j + 1}`);
        j++;
      }
      edits.push((tree) => {
        if (!safe(path)) throw new EditFail('unsafe', path);
        if (tree.get(path) === null) throw new EditFail('missing', path);
        tree.now.set(path, null);
      });
      i = j;
      continue;
    }
    if (line.startsWith('*** Update File: ')) {
      const path = line.slice('*** Update File: '.length).trim();
      const sec: { text: string; num: number }[] = [];
      let j = i + 1;
      while (j < last && !isSectionStart(lines[j] as string)) {
        sec.push({ text: lines[j] as string, num: j + 1 });
        j++;
      }
      while (sec.length > 0 && blank((sec[sec.length - 1] as { text: string }).text)) sec.pop();
      const { moveTo, chunks } = parseV4aUpdateBody(sec, i + 1);
      edits.push((tree) => {
        if (!safe(path)) throw new EditFail('unsafe', path);
        if (moveTo !== null && !safe(moveTo)) throw new EditFail('unsafe', moveTo);
        const before = tree.get(path);
        if (before === null) throw new EditFail('missing', path);
        if (moveTo !== null && tree.get(moveTo) !== null) throw new EditFail('exists', moveTo);
        const parts = fileParts(before);
        let lines = parts.lines.slice();
        let cursor = 0;
        for (const chunk of chunks) {
          if (chunk.anchor !== null) {
            let found = -1;
            for (let t = 0; t <= 2; t++) {
              if (strict && t > 0) break;
              for (let k = cursor; k < lines.length; k++) {
                if (norm(lines[k] as string, t) === norm(chunk.anchor as string, t)) {
                  found = k;
                  break;
                }
              }
              if (found >= 0) break;
            }
            if (found < 0) throw new EditFail('no-match', path);
            cursor = found + 1;
          }
          const { o, n } = splitBody(chunk.items);
          if (o.length === 0) {
            const at = chunk.eof ? lines.length : cursor;
            const ins = n.map((e) => e.text);
            lines.splice(at, 0, ...ins);
            cursor = at + ins.length;
            continue;
          }
          let tier = -1;
          let occ: number[] = [];
          for (let t = 0; t <= 2; t++) {
            if (strict && t > 0) break;
            const found = occurrences(lines, o, t, cursor, chunk.eof);
            if (found.length > 0) {
              tier = t;
              occ = found;
              break;
            }
          }
          if (tier < 0) throw new EditFail('no-match', path);
          const pos = occ[0] as number;
          const replacement = buildReplacement(lines, pos, o, n, tier);
          lines.splice(pos, o.length, ...replacement);
          cursor = pos + replacement.length;
        }
        const out = joinParts(lines, parts.br, parts.final);
        if (moveTo !== null) {
          tree.now.set(moveTo, out);
          tree.now.set(path, null);
          tree.moves.push({ from: path, to: moveTo });
        } else {
          tree.now.set(path, out);
        }
      });
      i = j;
      continue;
    }
    throw new HardExit(`error: parse ${i + 1}`);
  }
  return edits;
}

/** The output rows for a successful run (SPEC.md section 2): one line per changed path in UTF-8 byte order; a successful move is one `R <old> -> <new>` line sorting by the new path. */
function outputRows(tree: Tree): string[] {
  const rows = new Map<string, string>();
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p) as string | null;
    if (was === now) continue;
    rows.set(p, `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`);
  }
  for (const m of tree.moves) {
    if (tree.original(m.from) !== null && tree.now.get(m.from) === null && tree.original(m.to) === null && tree.now.get(m.to) !== null) {
      rows.delete(m.from);
      rows.delete(m.to);
      rows.set(m.to, `R ${m.from} -> ${m.to}`);
    }
  }
  return [...rows.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b))).map((k) => rows.get(k) as string);
}

/** Write every change to disk: create directories as needed, write files, remove deletions. */
function writeTree(tree: Tree): void {
  for (const [p, content] of tree.now) {
    if (content === null) {
      rmSync(p, { force: true });
    } else {
      const dir = dirname(p);
      if (dir !== '.') mkdirSync(dir, { recursive: true });
      writeFileSync(p, content, 'utf8');
    }
  }
}

interface RunResult {
  code: number;
  out: string[];
}

/** The command line (SPEC.md section 1) and the run's exit code and output. */
function run(args: string[]): RunResult {
  const usage = (): RunResult => ({ code: 2, out: ['error: usage'] });
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') {
      ended = true;
      continue;
    }
    if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=')) {
        if (format !== null) return usage();
        const v = a.slice('--format='.length);
        if (!FORMATS.includes(v)) return usage();
        format = v;
      } else if (a === '--check') {
        if (check) return usage();
        check = true;
      } else if (a === '--strict') {
        if (strict) return usage();
        strict = true;
      } else {
        return usage();
      }
    } else {
      pos.push(a);
    }
  }
  if (pos.length > 1) return usage();
  const patchFile = pos.length === 0 || pos[0] === '-' ? null : pos[0];
  let text: string;
  try {
    text = readFileSync(patchFile ?? 0, 'utf8');
  } catch {
    if (patchFile !== null) return { code: 2, out: ['error: no-patch'] };
    text = '';
  }
  const lines = patchParts(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else if (kind === 'v4a') edits = parseV4a(lines, strict);
    else edits = parseJson(text, lines);
    if (edits.length === 0) throw new HardExit('error: parse 1');
  } catch (e) {
    if (e instanceof HardExit) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: EditFail[] = [];
  for (const edit of edits) {
    const snap = new Map(tree.now);
    const movesLen = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof EditFail)) throw e;
      tree.restore(snap);
      tree.moves.length = movesLen;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }
  const rows = outputRows(tree);
  if (!check) writeTree(tree);
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
