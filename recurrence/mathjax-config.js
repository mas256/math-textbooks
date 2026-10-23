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
  // Break long display equations at operators to fit narrow screens; equations
  // without a break point still scroll horizontally.
  output: { displayOverflow: 'linebreak', linebreaks: { width: '100%' } },
  startup: { typeset: false },
};
