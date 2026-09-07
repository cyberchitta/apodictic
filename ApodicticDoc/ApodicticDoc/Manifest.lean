import Lean
import Apodictic.MarginalUtility

/-!
# `#manifest` — the manifest, derived

The document's manifest is kept by hand, so a reader is trusting that
it matches the signature it describes. This command derives it: it
walks a theorem's binder telescope and prints every binder SORTED BY
KIND, because a flat list destroys the very sort the audit turns on.

It lives in the document package, not the library. The library is the
trusted artifact and carries axioms, the action framework, and
theorems; this is tooling that reads them, and it is used where the
manifest is displayed.

## It reads one level into the vocabulary

A binder of a vocabulary type carries that structure's own `Prop`
fields, and whoever supplies the argument has to discharge them. They
are preconditions of the theorem in every sense that matters, and they
are invisible in the signature — which is exactly where an assumption
goes to hide. So the command projects each vocabulary binder's
structure and reports its `Prop` fields as a class of their own.

Only structures declared in the `Apodictic` library are opened: this
audit is not about mathlib's, and `Finset` alone would drag in
`nodup`. One level only — nothing here nests deeper, and a blind
recursion would walk into mathlib through the first field that
mentions it.

What the command cannot do is SORT what it finds there. Whether a
carried condition is definitional (it could not fail of a real
situation, so nothing is being assumed about the world) or
situational (it could fail, and then the theorem is silent) is a
judgement about the world, not about the term. The command surfaces
them; a human rules.

## What decides a binder's kind

- A *praxeological claim* is a binder whose type's head constant is
  DECLARED IN `Apodictic.Praxeology`. That is the project's own rule
  ("every universal claim is a structure in `Praxeology.lean`") asked
  of the environment rather than of a maintained list, so a new claim
  is classified the moment it is declared in the right place — and one
  declared in the wrong place shows up here as a situational
  condition, which is the failure worth seeing.
- A *condition on the data* is an instance-implicit binder.
- A *situational condition* is any other `Prop`.
- Everything else is *vocabulary*: what the claims are about.

## Its limits, all real

1. **The signature/conclusion line does not exist in Lean.** A
   theorem's type is one telescope; `∀ x ∈ s, P x` in the CONCLUSION
   is as much a binder as a hypothesis is. The command cuts at the
   first binder with macro scopes — the anonymous membership
   hypothesis that `∀ x ∈ s` desugars to — and reports how many it
   dropped. A conclusion binder the author NAMED, before that cut,
   is still listed under vocabulary (`atSmaller` in
   `marginal_utility`). Read the count.
2. **It reports the statement, not the proof.** A binder listed here
   may still do no work. What it adds over the linter is that it can
   SEE such a binder: `#lint only unusedArguments` is silenced by an
   `_` prefix, and this command marks that same binder "listed, does
   no work" instead. The two limits of the linter are stated in the
   document; this command closes one of them and neither closes the
   other (a hypothesis half of which is used looks whole to both).
-/

open Lean Meta Elab Command

namespace ApodicticDoc.Manifest

/-- The kinds a binder can have on a theorem's manifest, in the order
the document prints them. -/
inductive Kind where
  | claim | situational | data | vocabulary
  deriving BEq, Repr

def Kind.header : Kind → String
  | .claim => "praxeological claims"
  | .situational => "situational conditions"
  | .data => "conditions on the data"
  | .vocabulary => "vocabulary (what the claims are about)"

/-- The module a constant was declared in. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => some env.header.moduleNames[idx.toNat]!
  | none => none

/-- Is `n` declared in the module `Apodictic.Praxeology`? This is the
whole of the claim test — see the module docstring. -/
def inPraxeology (env : Environment) (n : Name) : Bool :=
  moduleOf env n == some `Apodictic.Praxeology

/-- Is `n` declared anywhere in the Apodictic library? Only those
structures are opened up — see the module docstring. -/
def inApodictic (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => m.getRoot == `Apodictic
  | none => false

def classify (env : Environment) (bi : BinderInfo) (ty : Expr) (isProp : Bool) : Kind :=
  if bi == .instImplicit then .data
  else if !isProp then .vocabulary
  else match ty.getAppFn.constName? with
    | some c => if inPraxeology env c then .claim else .situational
    | none => .situational

end ApodicticDoc.Manifest

open ApodicticDoc.Manifest in
/-- Print a theorem's manifest: every binder in its signature sorted
by kind, plus the logical background Lean itself supplies. See
`ApodicticDoc.Manifest` for what decides a kind and for the two
limits. -/
elab "#manifest " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown declaration {n}"
  let (binders, carried, dropped) ← liftTermElabM <|
      forallTelescopeReducing ci.type fun xs _ => do
    let mut acc := #[]
    let mut carried := #[]
    let mut dropped := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      -- Instance binders are machine-named by design and ARE signature.
      -- `hasMacroScopes` only, NOT `isInternal`: Lean counts a leading
      -- `_` as internal, so testing that hides `_firstStep` — the one
      -- binder whose idleness is a finding.
      if d.binderInfo != .instImplicit && d.userName.hasMacroScopes then
        dropped := xs.size - acc.size
        break
      let ty ← instantiateMVars d.type
      let isProp ← Meta.isProp ty
      let kind := classify env d.binderInfo ty isProp
      acc := acc.push (kind, d.binderInfo, d.userName, ← ppExpr ty)
      -- One level into the vocabulary: a structure argument carries its
      -- own `Prop` fields, and whoever supplies it discharges them.
      -- Apodictic structures only — `Finset` would contribute `nodup`.
      if kind == .vocabulary then
        if let some c := ty.getAppFn.constName? then
          if isStructure env c && inApodictic env c then
            for f in getStructureFields env c do
              let fieldTy ← instantiateMVars (← inferType (← Meta.mkProjection x f))
              if ← Meta.isProp fieldTy then
                carried := carried.push (s!"{d.userName}.{f}", ← ppExpr fieldTy)
    return (acc, carried, dropped)
  let mut out := s!"manifest of {n}\n"
  for k in [Kind.claim, Kind.situational, Kind.data, Kind.vocabulary] do
    let these := binders.filter (·.1 == k)
    if these.size > 0 then
      out := out ++ s!"\n  {k.header}:\n"
      for (_, bi, nm, ty) in these do
        let shown := if bi == .instImplicit then s!"[{ty}]" else s!"{nm} : {ty}"
        let mark := if nm.toString.startsWith "_" then "   -- listed, does no work" else ""
        out := out ++ s!"    {shown}{mark}\n"
  if carried.size > 0 then
    out := out ++ "\n  conditions carried by the vocabulary "
    out := out ++ "(not binders: discharged by\n  whoever supplies the argument):\n"
    for (nm, ty) in carried do
      out := out ++ s!"    {nm} : {ty}\n"
  let axs ← collectAxioms n
  out := out ++ s!"\n  logical background: {axs.toList}\n"
  if dropped > 0 then
    out := out ++ s!"\n  ({dropped} trailing binders belong to the conclusion, not the signature)\n"
  logInfo out
