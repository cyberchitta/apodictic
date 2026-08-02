/-!
# Axioms — the COMPLETE trusted base

Every `axiom` of the formalization lives in this file and nowhere
else. Nothing axiom-like — no axioms disguised as instance
assumptions, no hypotheses smuggled into theorem statements — may
live in any other module. The file is meant to be auditable at a
glance: read it and you have read everything the theorems rest on.

Every axiom declaration carries a docstring with two required fields:

- `Source:` citation to Mises / Rothbard, or "tacit"
- `Status:` explicit-in-tradition / suppressed-premise /
  our-reconstruction

No axioms yet. The first entry (the action axiom) awaits a design
decision reserved for the human — see CLAUDE.md.
-/
