const ACTIONS_URL = 'https://github.com/mas256/math-textbooks/actions/workflows/pages.yml';
const RUN_URL = /^https:\/\/github\.com\/mas256\/math-textbooks\/actions\/runs\/\d+$/;

export function apiEndpoint(value) {
  if (typeof value !== 'string' || !value.trim()) return null;
  const url = new URL(value.trim());
  if (url.protocol !== 'https:' || url.username || url.password || url.search || url.hash || url.pathname !== '/') {
    throw new Error('Invalid regeneration API URL');
  }
  return url.origin;
}

export async function initRegeneration() {
  const button = document.getElementById('regenerate-bank');
  const status = document.getElementById('regeneration-status');
  const link = document.getElementById('regeneration-run');
  let endpoint, busy = false, nextAllowedAt = 0, timer, requestWarning = '';

  function nextPoll() {
    clearTimeout(timer);
    timer = setTimeout(poll, 30000);
  }

  async function api(path, method = 'GET') {
    const response = await fetch(endpoint + path, { method, cache: 'no-store',
      credentials: 'omit', signal: AbortSignal.timeout(15000) });
    const data = await response.json();
    if (!response.ok && response.status !== 429) throw new Error('Regeneration API unavailable');
    return { data, limited: response.status === 429 };
  }

  function render(data) {
    nextAllowedAt = data.nextAllowedAt || 0;
    const run = data.run;
    const running = data.pending || run && run.status !== 'completed';
    button.disabled = busy || running || Date.now() < nextAllowedAt;
    link.href = run && RUN_URL.test(run.url) ? run.url : ACTIONS_URL;
    link.hidden = false;
    if (data.pending) status.textContent = '再生成を受け付けました。実行の開始を待っています。';
    else if (running) status.textContent = '問題バンクを再生成・検証しています。完了までしばらくかかります。';
    else if (run?.conclusion === 'success') status.textContent = '問題バンクの公開が完了しました。ページを再読み込みすると反映されます。';
    else if (run) status.textContent = '再生成が完了しませんでした。実行結果を確認してください。';
    else status.textContent = '最新の作問ルールで問題バンクを生成・検証し、公開します。';
    if (!running && Date.now() < nextAllowedAt) {
      const time = new Date(nextAllowedAt).toLocaleTimeString('ja-JP', { hour: '2-digit', minute: '2-digit' });
      status.textContent += ` 次の依頼は ${time} から受け付けます。`;
    }
    if (requestWarning) status.textContent = requestWarning + ' 最新の公開状況：' + status.textContent;
  }

  async function poll() {
    if (document.hidden || busy) { nextPoll(); return; }
    try { render((await api('/status')).data); }
    catch {
      status.textContent = '実行状況を取得できません。しばらくしてからもう一度お試しください。';
      button.disabled = Date.now() < nextAllowedAt;
      link.href = ACTIONS_URL;
      link.hidden = false;
    }
    nextPoll();
  }

  button.addEventListener('click', async () => {
    if (busy || !endpoint || button.disabled) return;
    busy = true;
    requestWarning = '';
    button.disabled = true;
    status.textContent = '再生成を依頼しています…';
    try {
      const { data, limited } = await api('/regenerate', 'POST');
      nextAllowedAt = data.nextAllowedAt || 0;
      if (limited) {
        status.textContent = '別の依頼を受け付け済みです。実行状況を確認します。';
      } else render({ ...data, pending: data.accepted });
    } catch {
      requestWarning = '今回の依頼の受付結果を確認できません。';
      status.textContent = requestWarning + ' 実行状況を取得しています。';
    } finally {
      busy = false;
      await poll();
    }
  });

  try {
    const response = await fetch('./regeneration-config.json', { cache: 'no-store' });
    if (!response.ok) throw new Error('Configuration unavailable');
    endpoint = apiEndpoint((await response.json()).endpoint);
    if (!endpoint) {
      status.textContent = '再生成の受付は準備中です。';
      return;
    }
    await poll();
  } catch {
    status.textContent = '再生成の受付を読み込めませんでした。ページを再読み込みしてください。';
  }
}

if (typeof document !== 'undefined') initRegeneration();
