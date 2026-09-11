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

The test is run on one law, the law of marginal utility, and on both
derivations the tradition gives it: Rothbard's in full, and Mises's
beside it, each rebuilt in Lean 4, a proof assistant. The law
itself is not Rothbard's. It is ordinary economics — he calls it "this
fundamental law of economics" and notes it is "sometimes known as the
law of diminishing marginal utility", and he is emphatic that other
writers reach it too, wrongly in his view, from psychology. What is
his is *how it is got*: deduced, he says, from the axiom of human
action. The deduction is what is supposed to carry the law to
certainty, so the deduction is what is audited here.

Spoken arguments run on enthymemes — steps that leave a premise
unstated because a reader will supply it without noticing. A proof
assistant supplies nothing. Anything the argument passes over in
silence has to be written down before the proof will go through, and
written somewhere a reader can find it.

**What the audit found.** The derivation goes through, and it needs one
praxeological claim to do it. That claim is not about anything the man
does. It credits him with a settled answer, held in advance, to what
he would do with every stock of horses smaller than the one he has —
and Rothbard's own restriction is that a man needs no such scale in
advance, because it shows up only in his concrete choices. He named
this law as the one exception to that rule, and what he offered to
warrant the exception is the derivation that needs it. A second demand, weaker,
is what the law's usual wording needs, and he grounds that one
elsewhere. Nothing here shows the law false, and nothing in the proof
runs in a circle. What is left is a question about the warrant — and
Mises, who gets to the law by another road, arrives at a premise of
the same shape and offers it none.

The case for all of it — the passages, the claim, the conditions, the
theorems, and the manifest each theorem carries — is in {ref "result"}[The Result].

{include 1 ApodicticDoc.Result}
