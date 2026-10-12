'use strict';
/*
 * IndieTaskTracker — Obsidian 看板插件（纯 JS 零构建）
 * 账本 = 一个 Markdown 文件（默认 任务看板.md），与 Tools/IndieTaskTracker.exe 共用同一格式：
 *   "## 列名"   = 列
 *   "### 卡标题" = 卡（标题一行，之后到下一个结构行之间是正文）
 * 外部改动（agent 写文件）→ vault modify 事件 → 看板自动重载。
 */

const { Plugin, ItemView, Notice, Setting, PluginSettingTab, TFile, TFolder, Menu, MarkdownRenderer, WorkspaceLeaf, normalizePath } = require('obsidian');

const VIEW_TYPE = 'itt-board-view';
const DEFAULTS = { boardPath: '任务看板.md', detailWidth: 420, rowBreaks: [] };

/* ============================================================
 * 解析 / 序列化（与 Tools/IndieTaskTracker/BoardDoc.cs 同口径）
 * ============================================================ */

function trimBullet(s) {
  const t = s.replace(/^\s+/, '');
  if (t.startsWith('- [ ] ')) return t.slice(6).trim();
  if (t.startsWith('- [x] ') || t.startsWith('- [X] ')) return t.slice(6).trim();
  if (t.startsWith('- ')) return t.slice(2).trim();
  return t.trim();
}

function parseBoard(text) {
  const lines = text.replace(/\r\n/g, '\n').split('\n');
  const doc = { preamble: [], columns: [] };
  let col = null, card = null, inSettings = false;
  const stray = [];

  const flushStray = () => {
    if (!col || stray.length === 0) { stray.length = 0; return; }
    if (col.cards.length === 0) {
      // Obsidian Kanban 旧格式兼容：无 ### 卡时，非缩进行开新卡，缩进行续正文
      let cur = null;
      for (const s of stray) {
        const indented = s[0] === ' ' || s[0] === '\t';
        if (!indented || !cur) { cur = { title: trimBullet(s), lines: [] }; col.cards.push(cur); }
        else cur.lines.push(s);
      }
    } else {
      col.cards[col.cards.length - 1].lines.push(...stray);
    }
    stray.length = 0;
  };

  for (const raw of lines) {
    if (inSettings) { if (raw.trimEnd() === '%%') inSettings = false; continue; }
    if (raw.startsWith('%% kanban:')) { inSettings = true; continue; }
    if (raw.startsWith('### ')) {
      flushStray();
      if (!col) { col = { name: '(未命名列)', cards: [] }; doc.columns.push(col); }
      const t = raw.slice(4).trim();
      card = { title: t.length ? t : '(无标题)', lines: [] };
      col.cards.push(card);
      continue;
    }
    if (raw.startsWith('## ') && (raw.length < 4 || raw[3] !== '#')) {
      flushStray();
      const t = raw.slice(3).trim();
      col = { name: t.length ? t : '(未命名列)', cards: [] };
      doc.columns.push(col);
      card = null;
      continue;
    }
    if (!col) { doc.preamble.push(raw); continue; }
    if (card) { card.lines.push(raw); continue; }
    if (raw.trim() === '') continue;
    stray.push(raw);
  }
  flushStray();

  while (doc.preamble.length && doc.preamble[doc.preamble.length - 1].trim() === '') doc.preamble.pop();
  for (const c of doc.columns) for (const cd of c.cards)
    while (cd.lines.length && cd.lines[cd.lines.length - 1].trim() === '') cd.lines.pop();
  return doc;
}

function serializeBoard(doc) {
  const sb = [];
  let atStart = true;
  if (doc.preamble.length) { for (const l of doc.preamble) sb.push(l + '\n'); atStart = false; }
  for (const col of doc.columns) {
    if (!atStart) sb.push('\n');
    sb.push('## ' + col.name + '\n');
    atStart = false;
    for (const card of col.cards) {
      sb.push('\n### ' + card.title + '\n');
      for (const l of card.lines) sb.push(l + '\n');
    }
  }
  return sb.join('');
}

function defaultBoardDoc() {
  const doc = { preamble: [], columns: [] };
  doc.columns.push({
    name: '📥 待办（你发布）', cards: [{
      title: '欢迎使用 IndieTaskTracker', lines: [
        '点卡片标题选中，右侧编辑正文；拖拽卡片换列（可插入任意位置）。',
        '',
        '- 发布任务：在「待办」列点 ＋，或文件夹右键「新建看板」',
        '- 做完的卡拖「🔍 待核对」，核对完拖「✅ 完成」',
        '- 本看板与 Tools/IndieTaskTracker.exe 共用同一份 md'
      ]
    }]
  });
  doc.columns.push({ name: '🔨 施工中（agent 做中）', cards: [] });
  doc.columns.push({ name: '🔍 待核对（agent 踢回）', cards: [] });
  doc.columns.push({ name: '✅ 完成', cards: [] });
  return doc;
}

/* ============================================================
 * 看板视图
 * ============================================================ */

class BoardView extends ItemView {
  constructor(leaf, plugin) {
    super(leaf);
    this.plugin = plugin;
    this.doc = null;
    this.file = null;
    this.filePath = null;         // 看板文件路径（setState 注入，随布局持久化）
    this._opened = false;
    this.sel = null;              // 主选卡（Card 对象引用）
    this.multiCards = [];         // 多选卡对象集合（含主选；长度>1 时详情区显示批量面板）
    this.cardEls = [];            // [{ el, col, card }]
    this.colEls = [];             // [{ el, cards, ci }]
    this.pendingWrite = false;
    this.writeTimer = null;
    this.suppressUntil = 0;       // 自己写盘后短暂忽略 modify 事件
    this.lastMtime = 0;
    this.dropMark = null;         // 拖拽落点 { col, idx }（idx=插入位置，允许同列重排）
    this._dragCards = null;       // 当前拖拽中的卡对象数组（多选=整批）
    this.detailW = this.plugin.settings.detailWidth || 420;
    this.detailEl = null;         // 详情面板容器（左侧，宽度可拖）
    this.previewMode = true;      // 详情面板：true=预览(渲染 Markdown，默认) false=编辑(textarea)
  }

  getViewType() { return VIEW_TYPE; }
  getDisplayText() { return 'IndieTaskTracker 看板'; }
  getIcon() { return 'clipboard-list'; }

  async setState(state, result) {
    const fp = state && state.file ? state.file : null;
    if (fp && fp !== this.filePath) {
      this.filePath = fp;
      if (this._opened) await this.loadBoard();   // 布局恢复后切文件
    }
    return super.setState(state, result);
  }

  getState() {
    const s = super.getState() || {};
    s.file = this.filePath;
    return s;
  }

  async onOpen() {
    this._opened = true;
    try {
      this.contentEl.addClass('itt-board-view');
      await this.loadBoard();
    } catch (e) {
      console.error('[ITT] onOpen 失败', e);
      this.contentEl.empty();
      this.contentEl.createDiv({ cls: 'itt-empty', text: '看板打开失败: ' + e.message });
    }
    // Esc：多选收起为单选（再按一次全清）
    this.registerDomEvent(window, 'keydown', e => {
      if (e.key !== 'Escape' || !this.multiCards.length) return;
      if (this.multiCards.length > 1) { this.multiCards = this.sel ? [this.sel] : []; }
      else this.clearSelection();
      this.refreshSelHighlight();
      if (this.detailEl) this.renderDetailInto(this.detailEl, false);
    });
  }

  async onClose() { await this.flushWrite(); }

  boardFile() {
    const p = this.filePath || this.plugin.settings.boardPath;
    const f = this.app.vault.getAbstractFileByPath(normalizePath(p));
    return f instanceof TFile ? f : null;
  }

  async loadBoard() {
    const f = this.boardFile();
    this.file = f;
    this.filePath = f ? f.path : (this.filePath || this.plugin.settings.boardPath);
    if (!f) { this.doc = null; this.sel = null; this.render(); return; }
    try {
      const text = await this.app.vault.read(f);
      this.doc = parseBoard(text);
      this.lastMtime = f.stat.mtime;
      this.sel = null;
      this.render();
    } catch (e) {
      console.error('[ITT] loadBoard 失败', e);
      this.doc = null; this.sel = null;
      this.contentEl.empty();
      this.contentEl.createDiv({ cls: 'itt-empty', text: '看板读取/渲染失败: ' + e.message });
    }
  }

  /* 外部改动（agent 写文件）：无挂起编辑时自动重载，选中按标题找回 */
  async onExternalModify() {
    const f = this.boardFile();
    if (!f || !this.doc) return;
    if (f.stat.mtime === this.lastMtime) return;
    if (Date.now() < this.suppressUntil || this.pendingWrite) return;
    const selTitle = this.sel ? this.sel.title : null;
    const text = await this.app.vault.read(f);
    this.doc = parseBoard(text);
    this.lastMtime = f.stat.mtime;
    this.sel = null; this.multiCards = [];
    if (selTitle) {
      for (const c of this.doc.columns) {
        const hit = c.cards.find(x => x.title === selTitle);
        if (hit) { this.selectCard(hit); break; }
      }
    }
    this.render();
  }

  /* ---- 写盘（500ms 防抖） ---- */
  scheduleWrite() {
    this.pendingWrite = true;
    if (this.writeTimer) clearTimeout(this.writeTimer);
    this.writeTimer = setTimeout(() => { this.writeTimer = null; this.flushWrite(); }, 500);
  }

  async flushWrite() {
    if (this.writeTimer) { clearTimeout(this.writeTimer); this.writeTimer = null; }
    if (!this.pendingWrite || !this.file || !this.doc) { this.pendingWrite = false; return; }
    this.pendingWrite = false;
    this.suppressUntil = Date.now() + 1500;
    this.lastMtime = Date.now();   // modify 事件回来自配
    try { await this.app.vault.modify(this.file, serializeBoard(this.doc)); }
    catch (e) { new Notice('看板保存失败: ' + e.message); }
  }

  /* ---- 数据操作 ---- */
  selColOf() { return this.doc.columns.find(c => c.cards.includes(this.sel)) || null; }

  selectCard(card) { this.sel = card; this.multiCards = [card]; }

  toggleSelect(card) {
    const i = this.multiCards.indexOf(card);
    if (i >= 0) {
      this.multiCards.splice(i, 1);
      if (this.sel === card) this.sel = this.multiCards[this.multiCards.length - 1] || null;
    } else {
      this.multiCards.push(card);
      this.sel = card;
    }
  }

  rangeSelect(card) {
    const fromCol = this.selColOf();
    const toCol = this.doc.columns.find(c => c.cards.includes(card));
    if (!fromCol || fromCol !== toCol) { this.selectCard(card); return; }
    const a = fromCol.cards.indexOf(this.sel), b = fromCol.cards.indexOf(card);
    const [lo, hi] = a <= b ? [a, b] : [b, a];
    this.multiCards = fromCol.cards.slice(lo, hi + 1);
    this.sel = card;
  }

  clearSelection() { this.sel = null; this.multiCards = []; }

  refreshSelHighlight() {
    for (const { el, card } of this.cardEls) el.classList.toggle('itt-sel', this.multiCards.includes(card));
  }

  /* 批量移动：cards=卡对象数组（按选择顺序），insertIdx=目标列插入位置（省略=列尾） */
  moveCardsTo(cards, toCi, insertIdx) {
    const to = this.doc.columns[toCi];
    if (!to || !cards.length) return;
    const bound = insertIdx == null ? to.cards.length : insertIdx;
    const before = cards.filter(c => to.cards.includes(c) && to.cards.indexOf(c) < bound).length;
    const set = new Set(cards);
    const removed = [];
    for (const col of this.doc.columns) {
      for (let i = col.cards.length - 1; i >= 0; i--) {
        if (set.has(col.cards[i])) removed.push(col.cards.splice(i, 1)[0]);
      }
    }
    const ordered = cards.filter(c => removed.includes(c));
    let idx = Math.max(0, Math.min(bound - before, to.cards.length));
    to.cards.splice(idx, 0, ...ordered);
    this.sel = ordered[0];
    this.multiCards = ordered;
    this.scheduleWrite();
    this.render();
  }

  /* 行段划分：rowBreaks（列名）标记「此列另起一行」 */
  getRowSegments() {
    const breaks = this.plugin.settings.rowBreaks || [];
    const segs = [[]];
    this.doc.columns.forEach((col, i) => {
      if (i > 0 && breaks.includes(col.name)) segs.push([]);
      segs[segs.length - 1].push(i);
    });
    return segs;
  }

  /* 整列 2D 移动：mode = 'left' | 'right'（同行相邻）| 'rowAbove' | 'rowBelow'（自成一行，紧贴目标行的上/下） */
  moveColumnTo(fromCi, mode, targetCi) {
    const cols = this.doc.columns;
    if (fromCi < 0 || fromCi >= cols.length || !cols[targetCi]) return;
    const breaks = this.plugin.settings.rowBreaks || (this.plugin.settings.rowBreaks = []);
    const moved = cols[fromCi], tgt = cols[targetCi];
    const segs = this.getRowSegments();
    const fromSeg = segs.find(s => s.includes(fromCi));
    const tgtSeg = segs.find(s => s.includes(targetCi));

    let insertAt, movedBr;   // 原始线性插入位 / 移动后是否行首
    if (mode === 'rowAbove') { insertAt = tgtSeg[0]; movedBr = true; }
    else if (mode === 'rowBelow') { insertAt = tgtSeg[tgtSeg.length - 1] + 1; movedBr = true; }
    else {
      insertAt = mode === 'left' ? targetCi : targetCi + 1;
      movedBr = mode === 'left' ? breaks.includes(tgt.name) : false;   // 左侧继承目标列行首身份；右侧=同行
    }

    const adjusted = insertAt > fromCi ? insertAt - 1 : insertAt;
    if (adjusted === fromCi) return;   // 没挪窝，什么都不动

    // 离开旧段：自己是行首就把行首让给旧段下一列
    if (breaks.includes(moved.name)) {
      breaks.splice(breaks.indexOf(moved.name), 1);
      const followers = fromSeg.filter(i => i !== fromCi && i > fromCi);
      if (followers.length && !breaks.includes(cols[followers[0]].name)) breaks.push(cols[followers[0]].name);
    }
    // left 抢目标列的行首身份（moved 接管行首，目标列退为同行后继）
    if (mode === 'left' && breaks.includes(tgt.name)) breaks.splice(breaks.indexOf(tgt.name), 1);
    if (movedBr && !breaks.includes(moved.name)) breaks.push(moved.name);

    const [col] = cols.splice(fromCi, 1);
    if (fromCi < insertAt) insertAt -= 1;
    cols.splice(insertAt, 0, col);

    // 自成一行的插入：把身后一列顶成新行首，保证 moved 独占一行
    const nextCol = cols[insertAt + 1];
    if (movedBr && nextCol && !breaks.includes(nextCol.name)) breaks.push(nextCol.name);

    this.plugin.saveSettings();
    this.scheduleWrite();
    this.render();
  }

  delCards(cards) {
    const set = new Set(cards);
    for (const col of this.doc.columns) col.cards = col.cards.filter(c => !set.has(c));
    this.clearSelection();
    this.scheduleWrite();
    this.render();
  }

  addCard(ci) {
    const col = this.doc.columns[ci];
    const card = { title: '新任务', lines: [] };
    col.cards.push(card);
    this.selectCard(card);
    this.scheduleWrite();
    this.render(true);
  }

  /* 拖拽落点：idx = 目标列插入位置（0..len）；卡片 dragover 传自身下标=插到它前面 */
  setDropIndicator(ci, idx) {
    if (this.dropMark && (this.dropMark.col !== ci || this.dropMark.idx !== idx)) this.clearDropIndicator();
    this.dropMark = { col: ci, idx };
    const col = this.doc.columns[ci];
    if (idx < col.cards.length) {
      const cardObj = col.cards[idx];
      const hit = this.cardEls.find(x => x.card === cardObj);
      if (hit) hit.el.classList.add('itt-drop-above');
    } else {
      const ce = this.colEls.find(x => x.ci === ci);
      if (ce) ce.cards.classList.add('itt-drop-tail');
    }
  }

  clearDropIndicator() {
    this.contentEl.querySelectorAll('.itt-drop-above, .itt-drop-tail')
      .forEach(el => el.classList.remove('itt-drop-above', 'itt-drop-tail'));
    this.dropMark = null;
  }

  /* 整列拖动落点指示：mode = 'left' | 'right' | 'rowAbove' | 'rowBelow' */
  setColDropIndicator(colEl, mode) {
    for (const x of this.colEls) {
      const on = x.el === colEl;
      x.el.classList.toggle('itt-drop-col-left', on && mode === 'left');
      x.el.classList.toggle('itt-drop-col-right', on && mode === 'right');
      x.el.classList.toggle('itt-drop-col-above', on && mode === 'rowAbove');
      x.el.classList.toggle('itt-drop-col-below', on && mode === 'rowBelow');
    }
  }

  clearColDropIndicator() {
    for (const x of this.colEls) x.el.classList.remove('itt-drop-col-left', 'itt-drop-col-right', 'itt-drop-col-above', 'itt-drop-col-below');
  }

  /* 移动卡（insertIdx 省略=追加到列尾；同列先移除后插入的索引自动补偿） */
  moveCardTo(fromCi, cardIdx, toCi, insertIdx) {
    const from = this.doc.columns[fromCi], to = this.doc.columns[toCi];
    if (!from || !to || cardIdx < 0 || cardIdx >= from.cards.length) return;
    const [card] = from.cards.splice(cardIdx, 1);
    let idx = insertIdx == null ? to.cards.length : insertIdx;
    if (fromCi === toCi && cardIdx < idx) idx -= 1;
    idx = Math.max(0, Math.min(idx, to.cards.length));
    to.cards.splice(idx, 0, card);
    this.sel = card;
    this.multiCards = [card];
    this.scheduleWrite();
    this.render();
  }

  addCard(ci) {
    const col = this.doc.columns[ci];
    const card = { title: '新任务', lines: [] };
    col.cards.push(card);
    this.selectCard(card);
    this.scheduleWrite();
    this.render(true);
  }

  delCard(card) {
    for (const col of this.doc.columns) {
      const k = col.cards.indexOf(card);
      if (k >= 0) col.cards.splice(k, 1);
    }
    this.multiCards = this.multiCards.filter(c => c !== card);
    this.sel = this.multiCards[this.multiCards.length - 1] || null;
    this.scheduleWrite();
    this.render();
  }

  addColumn() {
    this.doc.columns.push({ name: '新列', cards: [] });
    this.scheduleWrite();
    this.render();
  }

  renameColumn(ci, name) {
    const old = this.doc.columns[ci].name;
    name = name.trim() || '(未命名列)';
    this.doc.columns[ci].name = name;
    const b = this.plugin.settings.rowBreaks;   // 行首标记按列名记账，改名跟着走
    if (b) { const i = b.indexOf(old); if (i >= 0) b[i] = name; }
    this.scheduleWrite();
    this.render();
  }

  async createDefault() {
    const path = normalizePath(this.plugin.settings.boardPath);
    await this.app.vault.create(path, serializeBoard(defaultBoardDoc()));
    await this.loadBoard();
  }

  /* ---- 渲染 ---- */
  render(focusTitle = false) {
    const root = this.contentEl;
    root.empty();

    const head = root.createDiv({ cls: 'itt-head' });
    head.createSpan({ cls: 'itt-fname', text: this.file ? this.file.path : '（看板未创建）' });
    const tools = head.createDiv({ cls: 'itt-btnrow' });
    const refresh = tools.createEl('button', { text: '刷新' });
    refresh.addEventListener('click', () => this.loadBoard());
    const addColBtn = tools.createEl('button', { text: '＋ 列' });
    addColBtn.addEventListener('click', () => this.addColumn());
    const mdBtn = tools.createEl('button', { text: 'MD', attr: { title: '以 Markdown 打开（临时；想回看板点左栏图标）' } });
    mdBtn.addEventListener('click', () => {
      if (!this.filePath) return;
      this.plugin._mdOverride.add(this.leaf.id);
      this.leaf.setViewState({ type: 'markdown', state: { file: this.filePath } });
    });

    if (!this.doc) {
      const empty = root.createDiv({ cls: 'itt-empty' });
      empty.createSpan({ text: `看板文件不存在：${this.plugin.settings.boardPath}　` });
      const b = empty.createEl('button', { text: '创建默认看板' });
      b.addEventListener('click', () => this.createDefault());
      return;
    }

    const body = root.createDiv({ cls: 'itt-body' });

    // 详情面板在左，宽度可拖（分隔条）；列区在右
    const detail = body.createDiv({ cls: 'itt-detail' });
    detail.style.width = this.detailW + 'px';
    this.detailEl = detail;

    const splitter = body.createDiv({ cls: 'itt-splitter', attr: { title: '拖拽调宽' } });
    splitter.addEventListener('mousedown', e => {
      e.preventDefault();
      const startX = e.clientX, startW = this.detailW;
      const onMove = ev => {
        this.detailW = Math.max(260, Math.min(760, startW + (ev.clientX - startX)));
        detail.style.width = this.detailW + 'px';
      };
      const onUp = () => {
        document.removeEventListener('mousemove', onMove);
        document.removeEventListener('mouseup', onUp);
        document.body.classList.remove('itt-resizing');
        this.plugin.settings.detailWidth = this.detailW;
        this.plugin.saveSettings();
      };
      document.addEventListener('mousemove', onMove);
      document.addEventListener('mouseup', onUp);
      document.body.classList.add('itt-resizing');
    });

    const cols = body.createDiv({ cls: 'itt-cols' });
    this.cardEls = [];
    this.colEls = [];
    // 双层列表：外层竖排（行），内层横排（列）；rowBreaks（按列名）标记「此列另起一行」，行高紧贴内容
    const breaks = this.plugin.settings.rowBreaks || [];
    let row = cols.createDiv({ cls: 'itt-row' });
    this.doc.columns.forEach((col, ci) => {
      if (ci > 0 && breaks.includes(col.name)) row = cols.createDiv({ cls: 'itt-row' });
      this.renderCol(row, col, ci);
    });
    // 整列拖动三区：列顶 18% = 上面一行；中部 = 左/右（同行）；列底 22% = 下面一行
    cols.addEventListener('dragover', e => {
      if (!e.dataTransfer.types.includes('text/itt-col')) return;
      e.preventDefault(); e.dataTransfer.dropEffect = 'move';
      const colEl = e.target.closest('.itt-col');
      if (!colEl) { this.clearColDropIndicator(); return; }
      const r = colEl.getBoundingClientRect();
      const y = e.clientY - r.top;
      let mode;
      if (y < r.height * 0.18) mode = 'rowAbove';
      else if (y > r.height * 0.78) mode = 'rowBelow';
      else mode = e.clientX < r.left + r.width / 2 ? 'left' : 'right';
      this.setColDropIndicator(colEl, mode);
    });
    cols.addEventListener('dragleave', () => this.clearColDropIndicator());
    cols.addEventListener('drop', e => {
      if (!e.dataTransfer.types.includes('text/itt-col')) return;
      e.preventDefault();
      this.clearColDropIndicator();
      const fromCi = Number(e.dataTransfer.getData('text/itt-col'));
      const colEl = e.target.closest('.itt-col');
      if (!colEl || Number.isNaN(fromCi)) return;
      const hit = this.colEls.find(x => x.el === colEl);
      if (!hit) return;
      const r = colEl.getBoundingClientRect();
      const y = e.clientY - r.top;
      let mode;
      if (y < r.height * 0.18) mode = 'rowAbove';
      else if (y > r.height * 0.78) mode = 'rowBelow';
      else mode = e.clientX < r.left + r.width / 2 ? 'left' : 'right';
      this.moveColumnTo(fromCi, mode, hit.ci);
    });
    this.renderDetailInto(detail, focusTitle);
  }

  renderCol(parent, col, ci) {
    const el = parent.createDiv({ cls: 'itt-col' });
    el.addEventListener('dragover', e => {
      if (!e.dataTransfer.types.includes('text/itt-card')) return;
      e.preventDefault(); e.dataTransfer.dropEffect = 'move';
      el.classList.add('itt-drop');
      // 列头 / 首卡上方 = 插到列顶；末卡下方 / 列尾空区 = 追加；卡间空隙 = 就近插入
      const box = this.colEls.find(x => x.el === el).cards;
      const rects = [...box.children].map(c => c.getBoundingClientRect());
      if (e.target.closest('.itt-col-head') || !rects.length || e.clientY < rects[0].top) {
        this.setDropIndicator(ci, 0);
        return;
      }
      if (e.clientY > rects[rects.length - 1].bottom) {
        this.setDropIndicator(ci, this.doc.columns[ci].cards.length);
        return;
      }
      for (let k = 0; k < rects.length - 1; k++) {
        if (e.clientY >= rects[k].bottom && e.clientY <= rects[k + 1].top) {
          this.setDropIndicator(ci, k + 1);
          return;
        }
      }
      if (!this.dropMark || this.dropMark.col !== ci)
        this.setDropIndicator(ci, this.doc.columns[ci].cards.length);
    });
    el.addEventListener('dragleave', () => el.classList.remove('itt-drop'));
    el.addEventListener('drop', e => {
      e.preventDefault(); el.classList.remove('itt-drop');
      if (e.dataTransfer.types.includes('text/itt-col')) return;   // 列拖拽交给 container 处理
      const cards = this._dragCards;
      if (!cards || !cards.length) { this.clearDropIndicator(); return; }
      // 落点先读后清（clearDropIndicator 会置 null dropMark）；列头 = 插到列顶
      const onHead = !!e.target.closest('.itt-col-head');
      const idx = onHead ? 0
        : this.dropMark && this.dropMark.col === ci
          ? this.dropMark.idx
          : this.doc.columns[ci].cards.length;
      this.clearDropIndicator();
      if (cards.length > 1) this.moveCardsTo(cards, ci, idx);
      else {
        const fromCi = this.doc.columns.findIndex(c => c.cards.includes(cards[0]));
        if (fromCi >= 0) this.moveCardTo(fromCi, this.doc.columns[fromCi].cards.indexOf(cards[0]), ci, idx);
      }
      this._dragCards = null;
    });

    const head = el.createDiv({ cls: 'itt-col-head' });
    const grip = head.createSpan({ cls: 'itt-col-grip', text: '⠿', attr: { title: '拖动整列（左右移动）', draggable: 'true' } });
    grip.addEventListener('dragstart', e => {
      e.dataTransfer.setData('text/itt-col', String(ci));
      e.dataTransfer.effectAllowed = 'move';
    });
    grip.addEventListener('dragend', () => this.clearColDropIndicator());
    const nameEl = head.createSpan({ cls: 'itt-name', text: col.name });
    nameEl.addEventListener('dblclick', () => {
      const input = head.createEl('input', { type: 'text', value: col.name, cls: 'itt-rename' });
      nameEl.replaceWith(input);
      input.focus(); input.select();
      const commit = () => { this.renameColumn(ci, input.value); };
      input.addEventListener('blur', commit);
      input.addEventListener('keydown', e => { if (e.key === 'Enter') input.blur(); if (e.key === 'Escape') { input.value = col.name; input.blur(); } });
    });
    head.createSpan({ cls: 'itt-count', text: `(${col.cards.length})` });
    const tools = head.createDiv({ cls: 'itt-col-tools' });
    const add = tools.createEl('button', { text: '＋', attr: { title: '新卡' } });
    add.addEventListener('click', () => this.addCard(ci));
    const del = tools.createEl('button', { text: '✕', attr: { title: '删除列' } });
    del.addEventListener('click', () => {
      if (del.dataset.arm) {
        const b = this.plugin.settings.rowBreaks;   // 删列时清掉行首标记
        if (b) { const i = b.indexOf(col.name); if (i >= 0) b.splice(i, 1); }
        this.doc.columns.splice(ci, 1); this.sel = null; this.scheduleWrite(); this.render();
      }
      else { del.dataset.arm = '1'; del.textContent = '确认?'; setTimeout(() => { del.dataset.arm = ''; del.textContent = '✕'; }, 2500); }
    });

    const cards = el.createDiv({ cls: 'itt-cards' });
    this.colEls.push({ el, cards, ci });
    col.cards.forEach((card, k) => this.renderCard(cards, card, ci, k));
  }

  renderCard(parent, card, ci, k) {
    const sel = this.multiCards.includes(card);
    const el = parent.createDiv({
      cls: 'itt-card' + (sel ? ' itt-sel' : ''),
      text: card.title,
      attr: { draggable: 'true', title: '点击：编辑；Ctrl+点击：多选；Shift+点击：范围选；拖拽：移动（多选整批）；右键：菜单' }
    });
    this.cardEls.push({ el, card });
    el.addEventListener('click', e => {
      if (e.ctrlKey || e.metaKey) this.toggleSelect(card);
      else if (e.shiftKey && this.sel) this.rangeSelect(card);
      else this.selectCard(card);
      this.refreshSelHighlight();
      if (this.detailEl) this.renderDetailInto(this.detailEl, false);
    });
    el.addEventListener('dragstart', e => {
      this._dragCards = this.multiCards.includes(card) && this.multiCards.length > 1
        ? [...this.multiCards]
        : [card];
      e.dataTransfer.setData('text/itt-card', String(this._dragCards.length));
      e.dataTransfer.effectAllowed = 'move';
    });
    el.addEventListener('dragend', () => { this.clearDropIndicator(); this._dragCards = null; });
    el.addEventListener('dragover', e => {
      if (!e.dataTransfer.types.includes('text/itt-card')) return;
      e.preventDefault(); e.stopPropagation(); e.dataTransfer.dropEffect = 'move';
      const r = el.getBoundingClientRect();
      this.setDropIndicator(ci, k + (e.clientY < r.top + r.height / 2 ? 0 : 1));
    });
    el.addEventListener('contextmenu', e => {
      e.preventDefault(); e.stopPropagation();
      this.showCardMenu(e, card);
    });
  }

  showCardMenu(e, card) {
    const menu = new Menu();
    if (this.multiCards.includes(card) && this.multiCards.length > 1) {
      menu.addItem(mi => {
        mi.setTitle(`移动所选 ${this.multiCards.length} 张`).setIcon('arrow-right');
        const sub = mi.setSubmenu();
        this.doc.columns.forEach((c, j) => sub.addItem(s => s.setTitle(c.name).onClick(() => this.moveCardsTo([...this.multiCards], j, null))));
      });
      menu.addSeparator();
      menu.addItem(mi => mi.setTitle(`删除所选 ${this.multiCards.length} 张`).setIcon('trash').onClick(() => this.delCards([...this.multiCards])));
      menu.showAtMouseEvent(e);
      return;
    }
    const ci = this.doc.columns.findIndex(c => c.cards.includes(card));
    const k = ci >= 0 ? this.doc.columns[ci].cards.indexOf(card) : -1;
    menu.addItem(mi => mi.setTitle('重命名').setIcon('pencil').onClick(() => {
      this.selectCard(card);
      if (this.detailEl) this.renderDetailInto(this.detailEl, true);
    }));
    menu.addItem(mi => {
      mi.setTitle('移动到列').setIcon('arrow-right');
      const sub = mi.setSubmenu();
      this.doc.columns.forEach((c, j) => {
        if (j === ci) return;
        sub.addItem(s => s.setTitle(c.name).onClick(() => this.moveCardTo(ci, k, j)));
      });
    });
    menu.addSeparator();
    menu.addItem(mi => mi.setTitle('删除卡').setIcon('trash').onClick(() => this.delCard(card)));
    menu.showAtMouseEvent(e);
  }

  renderBatchPanel(d) {
    d.createSpan({ cls: 'itt-label', text: `已选 ${this.multiCards.length} 张卡（Esc 取消多选）` });
    const list = d.createDiv({ cls: 'itt-fblist' });
    for (const c of this.multiCards) list.createDiv({ cls: 'itt-fb', text: c.title });
    const row = d.createDiv({ cls: 'itt-btnrow' });
    row.createSpan({ cls: 'itt-label', text: '移动到列' });
    const sel = row.createEl('select');
    sel.createEl('option', { text: '选择目标列…', value: '-1' });
    this.doc.columns.forEach((c, k) => sel.createEl('option', { text: c.name, value: String(k) }));
    sel.addEventListener('change', () => {
      const j = Number(sel.value);
      if (j >= 0) this.moveCardsTo([...this.multiCards], j, null);
    });
    const del = row.createEl('button', { text: '删除所选', cls: 'itt-danger' });
    del.addEventListener('click', () => {
      if (del.dataset.arm) this.delCards([...this.multiCards]);
      else { del.dataset.arm = '1'; del.textContent = '确认删除?'; setTimeout(() => { del.dataset.arm = ''; del.textContent = '删除所选'; }, 2500); }
    });
  }

  renderDetailInto(d, focusTitle = false) {
    d.empty();
    if (this.multiCards.length > 1) { this.renderBatchPanel(d); return; }
    if (!this.sel) {
      d.createDiv({ cls: 'itt-empty', text: '← 点选一张卡（Ctrl+点击 多选），在这里编辑标题与正文' });
      return;
    }
    const col = this.selColOf();
    const card = this.sel;
    if (!col || !card) { this.clearSelection(); d.createDiv({ cls: 'itt-empty', text: '卡片已不存在' }); return; }

    d.createSpan({ cls: 'itt-label', text: '标题' });
    const ti = d.createEl('input', { type: 'text', value: card.title, cls: 'itt-title' });
    if (focusTitle) setTimeout(() => { ti.focus(); ti.select(); }, 0);
    ti.addEventListener('input', () => {
      card.title = ti.value.trim() ? ti.value : '(无标题)';
      const hit = this.cardEls.find(x => x.card === card);
      if (hit) hit.el.textContent = card.title;
      this.scheduleWrite();
    });

    // 编辑 / 预览 切换：编辑=textarea 纯文本；预览=Markdown 渲染（内链可点）
    const tabs = d.createDiv({ cls: 'itt-tabs' });
    const mkTab = (label, mode) => {
      const b = tabs.createEl('button', { text: label, cls: 'itt-tab' + (this.previewMode === mode ? ' itt-tab-on' : '') });
      b.addEventListener('click', () => {
        if (this.previewMode !== mode) { this.previewMode = mode; this.renderDetailInto(d, false); }
      });
    };
    mkTab('预览', true);
    mkTab('编辑', false);

    if (this.previewMode) {
      const pv = d.createDiv({ cls: 'itt-preview markdown-rendered' });
      try {
        MarkdownRenderer.render(this.app, card.lines.join('\n'), pv, this.file ? this.file.path : '', this);
      } catch (e) {
        console.error('[ITT] 预览渲染失败', e);
        pv.createDiv({ cls: 'itt-empty', text: '预览渲染失败: ' + e.message + '（切「编辑」仍可用）' });
      }
      pv.addEventListener('click', e => {
        const a = e.target.closest('a.internal-link');
        if (a) {
          e.preventDefault();
          this.app.workspace.openLinkText(a.getAttr('data-href') || a.getAttr('href'), this.file ? this.file.path : '', false);
        }
      });
    } else {
      d.createSpan({ cls: 'itt-label', text: '正文（支持 - [ ] 清单 / 缩进 / [[双链]]；行首别写 ## 或 ###）' });
    const ta = d.createEl('textarea', { cls: 'itt-content' });
    ta.value = card.lines.join('\n');
    ta.addEventListener('input', () => {
      const ls = ta.value.replace(/\r\n/g, '\n').split('\n');
      while (ls.length && ls[ls.length - 1].trim() === '') ls.pop();
      card.lines = ls;
      this.scheduleWrite();
    });
    }

    const ci = this.doc.columns.indexOf(col);
    const k = col.cards.indexOf(card);
    const row = d.createDiv({ cls: 'itt-btnrow' });
    row.createSpan({ cls: 'itt-label', text: '所在列' });
    const sel = row.createEl('select');
    this.doc.columns.forEach((c, kk) => {
      const o = sel.createEl('option', { text: c.name }); o.value = String(kk);
      if (kk === ci) o.selected = true;
    });
    sel.addEventListener('change', () => this.moveCardTo(ci, k, Number(sel.value)));
    const del = row.createEl('button', { text: '删除卡', cls: 'itt-danger' });
    del.addEventListener('click', () => {
      if (del.dataset.arm) this.delCard(card);
      else { del.dataset.arm = '1'; del.textContent = '确认删除?'; setTimeout(() => { del.dataset.arm = ''; del.textContent = '删除卡'; }, 2500); }
    });
  }
}

/* ============================================================
 * 插件壳
 * ============================================================ */

class IttSettingsTab extends PluginSettingTab {
  constructor(app, plugin) { super(app, plugin); this.plugin = plugin; }
  display() {
    const { containerEl } = this;
    containerEl.empty();
    new Setting(containerEl)
      .setName('看板文件路径')
      .setDesc('相对 vault 根（默认 任务看板.md）')
      .addText(t => t
        .setPlaceholder('任务看板.md')
        .setValue(this.plugin.settings.boardPath)
        .onChange(async v => {
          this.plugin.settings.boardPath = v.trim() || '任务看板.md';
          await this.plugin.saveSettings();
        }));
  }
}

module.exports = class IttPlugin extends Plugin {
  async onload() {
    this.settings = Object.assign({}, DEFAULTS, await this.loadData());
    this.addSettingTab(new IttSettingsTab(this.app, this));
    this.registerView(VIEW_TYPE, leaf => new BoardView(leaf, this));
    this.addRibbonIcon('clipboard-list', 'IndieTaskTracker 看板', () => this.activateView());
    this.addCommand({ id: 'open-board', name: '打开任务看板', callback: () => this.activateView() });
    // agent/外部写看板 → 自动刷新已打开的看板视图
    this.registerEvent(this.app.vault.on('modify', f => {
      if (!(f instanceof TFile)) return;
      if (normalizePath(f.path) !== normalizePath(this.settings.boardPath)) return;
      for (const leaf of this.app.workspace.getLeavesOfType(VIEW_TYPE)) {
        if (leaf.view && leaf.view.onExternalModify) leaf.view.onExternalModify();
      }
    }));
    // 老 Kanban 同款机制（src/main.ts registerMonkeyPatches 的 setViewState 补丁）：包住
    // WorkspaceLeaf.prototype.setViewState——任何 leaf 想以 Markdown 视图打开看板文件时，就地改写成看板视图。
    // 效果：点任务看板.md = 当前标签页原地变看板，永远不会多出第二个标签页。
    // 注意：原函数必须经 plugin._origSetViewState 闭包引用（老 Kanban 由 monkey-around 以 next 传入），
    //       直接写局部名会 ReferenceError，导致全库点开任何文件都抛异常。
    const plugin = this;
    this._loaded = false;           // 卸载/关库期间不劫持（对齐老 Kanban 的 self._loaded 守卫）
    this._mdOverride = new Set();   // 请求「以 Markdown 打开」的 leaf id（逃生门）
    const leafProto = WorkspaceLeaf.prototype;
    this._origSetViewState = leafProto.setViewState;
    leafProto.setViewState = function (state, ...rest) {
      try {
        if (
          plugin._loaded &&
          state && state.type === 'markdown' && state.state && typeof state.state.file === 'string' &&
          plugin.settings.boardPath &&
          !plugin._mdOverride.has(this.id) &&
          normalizePath(state.state.file) === normalizePath(plugin.settings.boardPath)
        ) {
          state = { ...state, type: VIEW_TYPE };
        }
      } catch (e) { console.error('[ITT] setViewState 补丁异常', e); }
      return plugin._origSetViewState.apply(this, [state, ...rest]);
    };
    this.register(() => { leafProto.setViewState = plugin._origSetViewState; });
    // 对齐老 Kanban 的 detach 补丁：leaf 关闭时清掉逃生门，之后点开看板文件可重新劫持
    this._origDetach = leafProto.detach;
    leafProto.detach = function (...args) {
      plugin._mdOverride.delete(this.id);
      return plugin._origDetach.apply(this, args);
    };
    this.register(() => { leafProto.detach = plugin._origDetach; });
    // 同文件去重：已有看板叶显示该文件时，再点文件/链接只聚焦那一叶，不再弹新标签页
    const ws = this.app.workspace;
    this._origOpenFile = ws.openFile;
    ws.openFile = async function (file, openState, options) {
      if (plugin._loaded && file instanceof TFile &&
          normalizePath(file.path) === normalizePath(plugin.settings.boardPath)) {
        const existing = ws.getLeavesOfType(VIEW_TYPE).find(l => l.view && l.view.filePath === file.path);
        if (existing) { ws.revealLeaf(existing); return existing.view; }
      }
      return plugin._origOpenFile.call(ws, file, openState, options);
    };
    this.register(() => { ws.openFile = plugin._origOpenFile; });
    // 叶级拦截：资源管理器点文件走的是 leaf.openFile（不经过 ws.openFile）。
    // 看板文件已开在某叶时，点击只聚焦那一叶；当前叶就是它时直接返回——杜绝重复标签页。
    this._origLeafOpenFile = leafProto.openFile;
    leafProto.openFile = async function (file, openState, options) {
      if (plugin._loaded && file instanceof TFile &&
          plugin.settings.boardPath &&
          !plugin._mdOverride.has(this.id) &&
          normalizePath(file.path) === normalizePath(plugin.settings.boardPath)) {
        const existing = ws.getLeavesOfType(VIEW_TYPE).find(l => l.view && l.view.filePath === file.path);
        if (existing) { ws.revealLeaf(existing); return existing.view; }
      }
      return plugin._origLeafOpenFile.apply(this, [file, openState, options]);
    };
    this.register(() => { leafProto.openFile = plugin._origLeafOpenFile; });
    // 文件夹右键 → 新建看板（对齐老 Kanban 的入口习惯：新建的 md 直接以看板打开在标签页里）
    this.registerEvent(this.app.workspace.on('file-menu', (menu, file, source) => {
      if (source !== 'file-explorer' || !(file instanceof TFolder)) return;
      menu.addItem(mi => mi.setTitle('新建看板').setIcon('clipboard-list').onClick(async () => {
        const base = (!file.path || file.path === '/') ? '新建看板' : `${file.path}/新建看板`;
        let target = `${base}.md`;
        for (let n = 1; this.app.vault.getAbstractFileByPath(normalizePath(target)); n++) target = `${base} ${n}.md`;
        const f = await this.app.vault.create(normalizePath(target), serializeBoard(defaultBoardDoc()));
        new Notice('看板已创建: ' + f.path);
        const leaf = this.app.workspace.getMostRecentLeaf();
        if (leaf) {
          await leaf.setViewState({ type: VIEW_TYPE, active: true, state: { file: f.path } });
          this.app.workspace.revealLeaf(leaf);
        }
      }));
    }));
    // 点开看板文件本身 → 由 setViewState 原型补丁接管（不再需要 file-open 拦截，避免双标签页）
    this._loaded = true;   // 补丁就绪，此后才开始劫持文件点开
  }

  async activateView() {
    const ws = this.app.workspace;
    // 已在主区标签页 → 直接聚焦
    for (const l of ws.getLeavesOfType(VIEW_TYPE)) {
      if (l.getRoot() === ws.rootSplit) { ws.revealLeaf(l); return; }
    }
    // 侧栏遗留的看板叶收掉（老布局），改开主区标签页——看板和笔记一样当标签页用
    for (const l of ws.getLeavesOfType(VIEW_TYPE)) {
      if (l.getRoot() === ws.leftSplit || l.getRoot() === ws.rightSplit) l.detach();
    }
    const leaf = ws.getLeaf('tab');
    this._mdOverride.delete(leaf && leaf.id);   // 回到看板模式，清除「以 Markdown 打开」逃生门
    await leaf.setViewState({
      type: VIEW_TYPE, active: true,
      state: { file: normalizePath(this.settings.boardPath) },
    });
    ws.revealLeaf(leaf);
  }

  async saveSettings() { await this.saveData(this.settings); }

  onunload() {
    this._loaded = false;   // 关库/重载期间不再劫持（对齐老 Kanban）
    const ws = this.app.workspace;
    if (this._origSetViewState) WorkspaceLeaf.prototype.setViewState = this._origSetViewState;
    if (this._origDetach) WorkspaceLeaf.prototype.detach = this._origDetach;
    if (this._origOpenFile) ws.openFile = this._origOpenFile;
    if (this._origLeafOpenFile) WorkspaceLeaf.prototype.openFile = this._origLeafOpenFile;
    // 看板叶退回 Markdown 视图，避免插件禁用/重载后留下无效视图（对齐老 Kanban 的 unload）
    for (const leaf of this.app.workspace.getLeavesOfType(VIEW_TYPE)) {
      const fp = leaf.view && leaf.view.filePath;
      if (fp) leaf.setViewState({ type: 'markdown', state: { file: fp }, popstate: true });
    }
  }
};

// 供无头自测使用（node 直接 require 本文件跑解析/序列化断言）
module.exports.parseBoard = parseBoard;
module.exports.serializeBoard = serializeBoard;
