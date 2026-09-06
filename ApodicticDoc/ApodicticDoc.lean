import VersoManual
import ApodicticDoc.Result

open Verso.Genre Manual

set_option pp.rawOnError true

/-
The archaeology part was DROPPED (human decision 2026-09-06): its
narrative duplicated `_notes/`, its docstring quotes duplicated
`Result`, and its crashes were rationale for an encoding the library
no longer uses. `ApodicticDoc.Rejected` went the same way once the
switch to structures made both crashes unreachable. History lives in
`_notes/`; this package emits one part.
-/
#doc (Manual) "Apodictic: Machine-Checked Praxeology" =>

%%%
authors := ["restlessronin"]
%%%

Mises claimed that the theorems of praxeology carry the same certainty
as the theorems of mathematics. They follow from the plain fact that
people act, he thought, as strictly as a theorem follows from its
axioms — and, being got that way, they are not the sort of claim
evidence can settle. No observation could confirm one, and none could
refute one. That is the claim being tested here.

The test is run on a single argument: Rothbard's derivation of the law
of marginal utility, rebuilt in Lean 4, a proof assistant. The law
itself is not his. It is ordinary economics — he calls it "this
fundamental law of economics" and notes it is "sometimes known as the
law of diminishing marginal utility", and he is emphatic that other
writers reach it too, wrongly in his view, from psychology. What is
his is *how it is got*: "derived from the fundamental axiom of human
action" (*MES* p. 27). The derivation is what carries the claim to
certainty, so the derivation is what is audited here.

Spoken arguments run on enthymemes — steps that leave a premise
unstated because a reader will supply it without noticing. A proof
assistant supplies nothing. Anything the argument passes over in
silence has to be written down before the proof will go through, and
written somewhere a reader can find it.

**The finding.** The law needs exactly one premise from praxeology,
and that premise is not about action. It is about what a man *would*
have done with a stock he never had. Rothbard's own derivation runs
that way: he sets six horses beside five and asks which want "the
larger stock would have satisfied".

Rothbard also sets a rule for what praxeology may use. It "may deal
with utilities only as deduced from the concrete actions of human
beings" — only what a man's actual choices show. His own law breaks
that rule. The man owns six horses; what he would have done with five
is not something any action of his shows.

This is not an objection from outside. The rule is Rothbard's, the
premise is Rothbard's, and the two do not fit.

It does not make the law wrong, either. The machine checked the
reasoning: the conclusion follows, and the proof uses only what the
statement lists. One question is left, and it is a narrow one — may
praxeology use that premise at all?

The argument follows Rothbard's own worked case — the six horses of
*Man, Economy, and State* — from beginning to end, and the Lean at the
close is about those same six horses.

{include 1 ApodicticDoc.Result}
