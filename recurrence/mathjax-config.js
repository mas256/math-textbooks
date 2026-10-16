window.MathJax = {
  tex: {
    inlineMath: [['\\(', '\\)']],
    displayMath: [['\\[', '\\]']],
    // Match TeX's \everymath{\displaystyle} without changing inline placement.
    preFilters: [({math}) => {
      if (!math.display && !/^\s*\\displaystyle\b/.test(math.math)) {
        math.math = '\\displaystyle ' + math.math;
      }
    }],
  },
  svg: { fontCache: 'local' },
  startup: { typeset: false },
};
