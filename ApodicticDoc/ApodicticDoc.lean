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
his is *how it is got*: deduced, he says, from the axiom of human
action. The deduction is what is supposed to carry the law to
certainty, so the deduction is what is audited here.

Spoken arguments run on enthymemes — steps that leave a premise
unstated because a reader will supply it without noticing. A proof
assistant supplies nothing. Anything the argument passes over in
silence has to be written down before the proof will go through, and
written somewhere a reader can find it.

**What the audit found.** The derivation goes through, and it needs one
praxeological claim to do it. That claim is subjunctive — it concerns
stocks the man never held, not anything he does. Rothbard's own
restriction on what praxeology may use rules such claims out, and he
exempted this law from that restriction by name, without argument. A
second subjunctive condition, weaker, is what the law's usual wording
needs, and it falls under the same restriction. Nothing here shows the
law false. What is left is a question about its warrant.

The case for all of it — the passages, the claim, the conditions, the
theorems, and the manifest each theorem carries — is in {ref "result"}[The Result].

{include 1 ApodicticDoc.Result}
