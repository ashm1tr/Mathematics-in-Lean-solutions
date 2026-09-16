# Mathematics in Lean — my solutions
![build](https://github.com/ashm1tr/Mathematics-in-Lean-solutions/actions/workflows/build.yml/badge.svg)
Working through [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
(Lean 4 + Mathlib). This is a clone of the
[upstream repository](https://github.com/leanprover-community/mathematics_in_lean)
with the exercises solved in place in `MIL/`, so `lake build` checks every proof.

**Progress:** Chapter 2 complete · Chapter 3 in progress · Chapters 4+ untouched.

**Build:**

```
lake exe cache get
lake build
```

**Remaining unsolved exercises:**

```
lake build 2>&1 | grep -c "declaration uses"
```

**Upstream updates:** `git fetch upstream && git merge upstream/master`