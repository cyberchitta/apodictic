# apodictic

**Machine-checked praxeology.**

> The theorems attained by correct praxeological reasoning are not only
> perfectly certain and incontestable, like the correct mathematical
> theorems. They refer, moreover with the full rigidity of their
> **apodictic** certainty and incontestability to the reality of action
> as it appears in life and history. Praxeology conveys exact and
> precise knowledge of real things.
>
> — Mises, *Human Action*, ch. II §3, "The A Priori and Reality"
> (Scholar's Edition, p. 39; emphasis added)

Mathematical theorems can be machine-checked. So let's check.

## What this is

An attempt to formalize the deductive core of Austrian praxeology
(Mises, Rothbard) in Lean 4, carrying the theorem ladder — marginal
utility, the law of returns, exchange, price bounds, time preference —
from an explicit, auditable axiom base.

The method is **axiom archaeology**: the verbal deductions in *Human
Action* and *Man, Economy, and State* are enthymemes, arguments with
suppressed premises. A proof assistant refuses to accept an enthymeme.
Every hidden assumption must surface as a named axiom, with its pedigree
documented in the axiom's docstring — source (Mises/Rothbard citation,
or "tacit") and status: explicit in the tradition, suppressed premise,
or our reconstruction.

The interesting output is not "praxeology: true or false." It is the
minimal axiom list under each theorem. `#print axioms marginal_utility`
is the whole point.

## What this is not

- Not neoclassical choice theory in a hat. The formalization aims to
  honor what praxeology insists on: ordinal-only preference, demonstrated
  preference, real time, no cardinal utility, no given ends–means data
  hanging in a Platonic space. Where honoring these makes proofs harder,
  the difficulty is the finding.
- Not advocacy. If a theorem needs an axiom Rothbard denied using,
  that goes in the paper. If the deductions go through cleanly, that
  goes in the paper too.

## Structure

Two lake packages:

```
Apodictic/             -- the library. Depends on mathlib only; always
                       -- builds standalone. The trusted artifact.
  Apodictic/
    Axioms.lean        -- the complete trusted base, nothing else
    Action.lean        -- agents, ends, means, the action framework
    MarginalUtility.lean -- first theorem target
ApodicticDoc/          -- Verso document package, depends on the library.
                       -- The connected essay: axiom archaeology,
                       -- findings, design decisions, and rejected
                       -- encodings as type-checked Lean code.
```

If Verso lags a Lean toolchain bump, the document waits; the library's
toolchain is never downgraded to accommodate it. Proofs over prose.

## Status

Early. Current milestone: formalize the action framework and
machine-check the law of marginal utility (Rothbard's allocation
version), with an honest treatment of the homogeneous-units /
indifference problem.

## Reading

- Mises, *Human Action*, chs. 1–7
- Rothbard, *Man, Economy, and State*, ch. 1
- Nozick, "On Austrian Methodology" (1977) — the critique the
  formalization must survive, not dodge
