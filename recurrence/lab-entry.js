"use strict";
// Keep published problem and 14-question-set links attached to their original
// immutable bank. Newly generated problems are shared through saved Recipes.
(() => {
  const current = new URL(window.location.href);
  if (current.searchParams.has("problem") || current.searchParams.has("batch")) {
    const destination = new URL("./textbook.html", current);
    destination.search = current.search;
    destination.hash = current.hash;
    window.location.replace(destination.href);
  }
})();
