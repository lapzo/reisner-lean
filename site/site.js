(() => {
  function revealHash() {
    if (!location.hash) return;
    let target;
    try { target = document.getElementById(decodeURIComponent(location.hash.slice(1))); }
    catch { return; }
    if (!target) return;
    for (let p = target; p; p = p.parentElement) {
      if (p.tagName === 'DETAILS') p.open = true;
    }
    if (target.closest('[hidden]') && window.resetBlueprintFilters) window.resetBlueprintFilters();
    requestAnimationFrame(() => target.scrollIntoView({block: 'start', behavior: 'instant'}));
  }
  addEventListener('hashchange', revealHash);
  addEventListener('load', revealHash);

  document.querySelectorAll('.copy-button').forEach(button => {
    button.addEventListener('click', async () => {
      const block = button.closest('.code-wrap');
      const value = Array.from(block.querySelectorAll('.source-line')).map(line => line.textContent).join('\n');
      try {
        if (!navigator.clipboard) throw new Error('Clipboard unavailable');
        await navigator.clipboard.writeText(value);
        button.textContent = 'Copied';
      } catch {
        const range = document.createRange();
        range.selectNodeContents(block.querySelector('code'));
        const selection = getSelection(); selection.removeAllRanges(); selection.addRange(range);
        button.textContent = 'Code selected';
      }
      setTimeout(() => { button.textContent = 'Copy'; }, 1800);
    });
  });

  const headings = [...document.querySelectorAll('main h2[id]')];
  if ('IntersectionObserver' in window) {
    const observer = new IntersectionObserver(entries => {
      for (const entry of entries) if (entry.isIntersecting) {
        document.querySelectorAll('.toc a').forEach(link => {
          link.classList.toggle('active', link.hash === '#' + entry.target.id);
        });
      }
    }, {rootMargin: '-10% 0px -70% 0px'});
    headings.forEach(heading => observer.observe(heading));
  }

  const search = document.getElementById('node-search');
  const status = document.getElementById('node-status');
  const nodes = [...document.querySelectorAll('.blueprint-node')];
  const count = document.getElementById('filter-count');
  if (search && status) {
    const filter = () => {
      const term = search.value.trim().toLocaleLowerCase();
      let visible = 0;
      nodes.forEach(node => {
        const matches = node.textContent.toLocaleLowerCase().includes(term) &&
          (status.value === 'all' || node.dataset.status === status.value);
        node.hidden = !matches; if (matches) visible++;
      });
      document.querySelectorAll('.blueprint-section[data-node-section="true"]').forEach(section => {
        section.hidden = !section.querySelector('.blueprint-node:not([hidden])');
      });
      count.textContent = `${visible} of ${nodes.length} nodes shown`;
      document.getElementById('empty-state').hidden = visible !== 0;
    };
    search.addEventListener('input', filter);
    status.addEventListener('change', filter);
    window.resetBlueprintFilters = () => { search.value = ''; status.value = 'all'; filter(); };
    document.getElementById('reset-filters').addEventListener('click', window.resetBlueprintFilters);
  }

  const viewport = document.querySelector('.graph-viewport');
  if (viewport) {
    const svg = viewport.querySelector('svg'); let zoom = 1;
    const setZoom = value => {
      zoom = Math.max(1, Math.min(3, value));
      svg.style.width = (zoom * 100) + '%';
      document.getElementById('zoom-level').textContent = Math.round(zoom * 100) + '%';
    };
    document.getElementById('zoom-in').addEventListener('click', () => setZoom(zoom + .25));
    document.getElementById('zoom-out').addEventListener('click', () => setZoom(zoom - .25));
    document.getElementById('zoom-fit').addEventListener('click', () => {
      setZoom(1); viewport.scrollTo(0, 0);
    });
  }
})();
