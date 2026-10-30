/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.TPE.SlicedPolicies
import Cedar.Thm.TPE.SlicedPoliciesActionInAny
import Cedar.Thm.TPE.SlicedPoliciesDropped
import Cedar.Thm.External.Decompose
import Cedar.Thm.Data

/-!
Correctness of partial authorization with policies sliced for one request
environment.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.TPE
open Cedar.Validation

/-- `sliced` is obtained from `full` by deleting residual policies that are
    already the literal result `false`. Retained residual policies are
    unchanged and remain in order. -/
inductive ResidualPolicies.DropFalse : List ResidualPolicy → List ResidualPolicy → Prop where
  | nil : ResidualPolicies.DropFalse [] []
  | keep {r full sliced} : ResidualPolicies.DropFalse full sliced →
      ResidualPolicies.DropFalse (r :: full) (r :: sliced)
  | drop {r full sliced} : r.isFalse = true → ResidualPolicies.DropFalse full sliced →
      ResidualPolicies.DropFalse (r :: full) sliced

/-- The observable refinement produced by dropping known-false policies. -/
structure _root_.Cedar.TPE.Response.SliceRefines (sliced full : Cedar.TPE.Response) : Prop where
  decision : sliced.decision = full.decision
  satisfiedPermits : sliced.satisfiedPermits = full.satisfiedPermits
  errorPermits : sliced.errorPermits = full.errorPermits
  residualPermits : sliced.residualPermits = full.residualPermits
  satisfiedForbids : sliced.satisfiedForbids = full.satisfiedForbids
  errorForbids : sliced.errorForbids = full.errorForbids
  residualForbids : sliced.residualForbids = full.residualForbids
  falsePermits : sliced.falsePermits ⊆ full.falsePermits
  falseForbids : sliced.falseForbids ⊆ full.falseForbids
  residuals : ResidualPolicies.DropFalse full.residuals sliced.residuals
  reauthorize : ∀ req es, sliced.reauthorize req es = full.reauthorize req es

private theorem isFalse_implies_residual_eq_false {r : ResidualPolicy} (h : r.isFalse = true) :
    ∃ ty, r.residual = .val (.prim (.bool false)) ty := by
  cases r with
  | mk id effect residual =>
    cases residual <;> simp [ResidualPolicy.isFalse, Residual.isFalse] at h
    rename_i v ty
    cases v <;> simp_all
    rename_i p
    cases p <;> simp_all
    rename_i b
    cases b <;> simp_all

private theorem false_policy_nonfalse_filters {r : ResidualPolicy} (h : r.isFalse = true) (effect : Effect) :
    r.satisfiedWithEffect effect = none ∧
    r.erroredWithEffect effect = none ∧
    r.residualWithEffect effect = none := by
  obtain ⟨ty, hr⟩ := isFalse_implies_residual_eq_false h
  cases r
  simp_all [ResidualPolicy.satisfiedWithEffect, ResidualPolicy.satisfied,
    ResidualPolicy.erroredWithEffect, ResidualPolicy.hasError,
    ResidualPolicy.residualWithEffect, ResidualPolicy.isResidual,
    ResidualPolicy.isFalse, Residual.isFalse, Residual.isTrue, Residual.isError]

private theorem false_policy_reauthorize_filters {r : ResidualPolicy} (h : r.isFalse = true)
    (effect : Effect) (req : Request) (es : Entities) :
    Cedar.TPE.Response.reauthorize.satisfiedWithEffect effect r req es = none ∧
    Cedar.TPE.Response.reauthorize.errored r req es = none := by
  obtain ⟨ty, hr⟩ := isFalse_implies_residual_eq_false h
  cases r
  simp_all [Cedar.TPE.Response.reauthorize.satisfiedWithEffect,
    Cedar.TPE.Response.reauthorize.satisfied, Cedar.TPE.Response.reauthorize.errored,
    Cedar.TPE.Response.reauthorize.hasError, Residual.evaluate]

private theorem dropFalse_filterMap_nonfalse
    {full sliced : List ResidualPolicy}
    (h : ResidualPolicies.DropFalse full sliced)
    (f : ResidualPolicy → Option PolicyID)
    (hfalse : ∀ r, r.isFalse = true → f r = none) :
    sliced.filterMap f = full.filterMap f := by
  induction h with
  | nil => rfl
  | keep h ih => simp only [List.filterMap_cons, ih]
  | drop hr h ih => simp only [List.filterMap_cons, hfalse _ hr, ih]

private theorem dropFalse_subset {full sliced : List ResidualPolicy}
    (h : ResidualPolicies.DropFalse full sliced) : sliced ⊆ full := by
  induction h with
  | nil => simp
  | keep h ih => exact List.cons_subset_cons _ ih
  | drop hr h ih =>
    intro r hrmem
    exact List.mem_cons_of_mem _ (ih hrmem)

private theorem dropFalse_filterMap_false_subset
    {full sliced : List ResidualPolicy}
    (h : ResidualPolicies.DropFalse full sliced) (effect : Effect) :
    sliced.filterMap (ResidualPolicy.falseWithEffect effect) ⊆
      full.filterMap (ResidualPolicy.falseWithEffect effect) := by
  intro pid hpid
  obtain ⟨r, hr, heq⟩ := List.mem_filterMap.mp hpid
  exact List.mem_filterMap.mpr ⟨r, dropFalse_subset h hr, heq⟩

private theorem dropFalse_reauthorize
    {full sliced : List ResidualPolicy}
    (h : ResidualPolicies.DropFalse full sliced) (req : Request) (es : Entities) :
    (Cedar.TPE.Response.reauthorize
      (Cedar.TPE.isAuthorizedFromResiduals sliced) req es) =
    (Cedar.TPE.Response.reauthorize
      (Cedar.TPE.isAuthorizedFromResiduals full) req es) := by
  have hs (effect : Effect) := dropFalse_filterMap_nonfalse h
    (fun r => Cedar.TPE.Response.reauthorize.satisfiedWithEffect effect r req es)
    (fun r hr => (false_policy_reauthorize_filters hr effect req es).1)
  have he := dropFalse_filterMap_nonfalse h
    (fun r => Cedar.TPE.Response.reauthorize.errored r req es)
    (fun r hr => (false_policy_reauthorize_filters hr .permit req es).2)
  simp only [Cedar.TPE.Response.reauthorize, Cedar.TPE.isAuthorizedFromResiduals]
  simp only [Cedar.TPE.Response.reauthorize.satisfiedPolicies,
    Cedar.TPE.Response.reauthorize.errorPolicies, hs, he]
  rfl

/-- Dropping literal-false residual policies preserves all authorization
    categories except that the reported false-policy sets may shrink. -/
theorem isAuthorizedFromResiduals_dropFalse
    {full sliced : List ResidualPolicy}
    (h : ResidualPolicies.DropFalse full sliced) :
    (isAuthorizedFromResiduals sliced).SliceRefines (isAuthorizedFromResiduals full) := by
  have hs (effect : Effect) := dropFalse_filterMap_nonfalse h
    (ResidualPolicy.satisfiedWithEffect effect)
    (fun r hr => (false_policy_nonfalse_filters hr effect).1)
  have he (effect : Effect) := dropFalse_filterMap_nonfalse h
    (ResidualPolicy.erroredWithEffect effect)
    (fun r hr => (false_policy_nonfalse_filters hr effect).2.1)
  have hr (effect : Effect) := dropFalse_filterMap_nonfalse h
    (ResidualPolicy.residualWithEffect effect)
    (fun r hfalse => (false_policy_nonfalse_filters hfalse effect).2.2)
  have hs' (effect : Effect) :
      isAuthorizedFromResiduals.satisfiedPolicies effect sliced =
        isAuthorizedFromResiduals.satisfiedPolicies effect full := by
    simp [isAuthorizedFromResiduals.satisfiedPolicies, hs effect]
  have he' (effect : Effect) :
      isAuthorizedFromResiduals.errorPolicies effect sliced =
        isAuthorizedFromResiduals.errorPolicies effect full := by
    simp [isAuthorizedFromResiduals.errorPolicies, he effect]
  have hr' (effect : Effect) :
      isAuthorizedFromResiduals.residualPolicies effect sliced =
        isAuthorizedFromResiduals.residualPolicies effect full := by
    simp [isAuthorizedFromResiduals.residualPolicies, hr effect]
  constructor
  · simp [isAuthorizedFromResiduals, hs', hr']
  · exact hs' .permit
  · exact he' .permit
  · exact hr' .permit
  · exact hs' .forbid
  · exact he' .forbid
  · exact hr' .forbid
  · rw [Set.subset_def]
    intro pid hpid
    simp only [isAuthorizedFromResiduals, isAuthorizedFromResiduals.falsePolicies,
      Set.mem_make] at hpid ⊢
    exact dropFalse_filterMap_false_subset h .permit hpid
  · rw [Set.subset_def]
    intro pid hpid
    simp only [isAuthorizedFromResiduals, isAuthorizedFromResiduals.falsePolicies,
      Set.mem_make] at hpid ⊢
    exact dropFalse_filterMap_false_subset h .forbid hpid
  · exact h
  · exact dropFalse_reauthorize h

/-- A retained policy has the same residual when slicing and evaluation use the
    same schema. The only non-structural case is `action in [...]`, whose
    filtered list is equivalent because the request action's ancestors are
    known. -/
private theorem evaluatePolicy_slice_keep_same_schema
    {schema : Schema} {p p' : Policy} {req : PartialRequest}
    {es : PartialEntities} {env : TypeEnv} {r : Residual}
    (hreq : validatePartialRequest schema req = .ok env)
    (hents : entitiesIsValid schema es = true)
    (hanc : (es.ancestors req.action).isSome = true)
    (hslice : Cedar.TPE.Policy.sliceForRequestEnv p env = some p')
    (heval : evaluatePolicy schema p req es = .ok r) :
    evaluatePolicy schema p' req es = .ok r := by
  rcases p with ⟨id, effect, ⟨ps⟩, asc, ⟨rs⟩, cs⟩
  cases asc with
  | actionInAny uids =>
    exact SlicedPoliciesActionInAny.evaluatePolicy_actionInAny_slice_keep
      hreq hents hanc hslice rfl heval
  | actionScope actionScope =>
    cases actionScope <;>
      simp only [Cedar.TPE.Policy.sliceForRequestEnv, ActionScope.sliceForAction,
        bind, Option.bind] at hslice
    all_goals
      repeat' split at hslice
      all_goals simp_all

/-- Evaluate a policy and retain its identifier and effect with the residual.
    This factors the local worker used by `isAuthorized` into a proof-facing
    definition. -/
private def evalResidualPolicy (schema : Schema) (p : Policy) (req : PartialRequest)
    (es : PartialEntities) : Except Cedar.TPE.Error ResidualPolicy := do
  pure ⟨p.id, p.effect, ← evaluatePolicy schema p req es⟩

private def evalResidualPolicies (schema : Schema) (policies : Policies)
    (req : PartialRequest) (es : PartialEntities) :
    Except Cedar.TPE.Error (List ResidualPolicy) :=
  policies.mapM (evalResidualPolicy schema · req es)

private theorem isAuthorized_eq_evalResidualPolicies
    (schema : Schema) (policies : Policies) (req : PartialRequest)
    (es : PartialEntities) :
    isAuthorized schema policies req es = (do
      let residuals ← evalResidualPolicies schema policies req es
      pure (isAuthorizedFromResiduals residuals)) := by
  rfl

/-- Pointwise correctness for dropped and retained policies lifts to the
    ordered `DropFalse` relation over the complete residual lists. -/
private theorem evalResidualPolicies_dropFalse
    {full sliced : Schema} {policies slicedPolicies : Policies}
    {req : PartialRequest} {es : PartialEntities}
    {fullResiduals : List ResidualPolicy}
    (slice : Policy → Option Policy)
    (hsliced : slicedPolicies = policies.filterMap slice)
    (hdrop : ∀ p r, slice p = none →
      evalResidualPolicy full p req es = .ok r → r.isFalse = true)
    (hkeep : ∀ p p' r, slice p = some p' →
      evalResidualPolicy full p req es = .ok r →
      evalResidualPolicy sliced p' req es = .ok r)
    (hfull : evalResidualPolicies full policies req es = .ok fullResiduals) :
    ∃ slicedResiduals,
      evalResidualPolicies sliced slicedPolicies req es = .ok slicedResiduals ∧
      ResidualPolicies.DropFalse fullResiduals slicedResiduals := by
  subst hsliced
  induction policies generalizing fullResiduals with
  | nil =>
    simp only [evalResidualPolicies, List.mapM_nil, pure, Except.pure,
      Except.ok.injEq] at hfull ⊢
    subst hfull
    exact ⟨[], rfl, .nil⟩
  | cons p ps ih =>
    simp only [evalResidualPolicies]
    simp only [evalResidualPolicies, List.mapM_cons] at hfull
    cases hp : evalResidualPolicy full p req es with
    | error _ => simp [hp] at hfull
    | ok r =>
      simp only [hp, bind, Except.bind] at hfull
      cases hps : evalResidualPolicies full ps req es with
      | error e =>
        have hpsm : List.mapM (evalResidualPolicy full · req es) ps = .error e := hps
        rw [hpsm] at hfull
        contradiction
      | ok rs =>
        have hpsm : List.mapM (evalResidualPolicy full · req es) ps = .ok rs := hps
        rw [hpsm] at hfull
        simp only [pure, Except.pure, Except.ok.injEq] at hfull
        subst fullResiduals
        cases hslice : slice p with
        | none =>
          simp only [List.filterMap_cons, hslice]
          obtain ⟨srs, hsrs, hrel⟩ := ih hps
          exact ⟨srs, hsrs, .drop (hdrop p r hslice hp) hrel⟩
        | some p' =>
          simp only [List.filterMap_cons, hslice, List.mapM_cons]
          rw [hkeep p p' r hslice hp]
          simp only [bind, Except.bind]
          obtain ⟨srs, hsrs, hrel⟩ := ih hps
          change List.mapM (evalResidualPolicy sliced · req es)
            (List.filterMap slice ps) = .ok srs at hsrs
          refine ⟨r :: srs, ?_, .keep hrel⟩
          rw [hsrs]
          rfl

/-- Authorization-level assembly lemma. A slicing transformation refines the
    full result once each omitted policy is known false and every retained
    policy has the same residual under the sliced schema. -/
theorem isAuthorized_refines_of_policy_slice
    {full sliced : Schema} {policies : Policies}
    {req : PartialRequest} {es : PartialEntities} {rf : Cedar.TPE.Response}
    (slice : Policy → Option Policy)
    (hdrop : ∀ p r, slice p = none →
      evalResidualPolicy full p req es = .ok r → r.isFalse = true)
    (hkeep : ∀ p p' r, slice p = some p' →
      evalResidualPolicy full p req es = .ok r →
      evalResidualPolicy sliced p' req es = .ok r)
    (hbase : isAuthorized full policies req es = .ok rf) :
    ∃ rs, isAuthorized sliced (policies.filterMap slice) req es = .ok rs ∧
      rs.SliceRefines rf := by
  rw [isAuthorized_eq_evalResidualPolicies] at hbase ⊢
  cases hfull : evalResidualPolicies full policies req es with
  | error _ => simp [hfull] at hbase
  | ok fullResiduals =>
    simp only [hfull, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at hbase
    subst rf
    obtain ⟨slicedResiduals, hsliced, hrel⟩ :=
      evalResidualPolicies_dropFalse slice rfl hdrop hkeep hfull
    rw [hsliced]
    exact ⟨isAuthorizedFromResiduals slicedResiduals, rfl,
      isAuthorizedFromResiduals_dropFalse hrel⟩

private theorem sliceForRequestEnv_preserves_id_effect
    {p p' : Policy} {env : TypeEnv}
    (h : Cedar.TPE.Policy.sliceForRequestEnv p env = some p') :
    p'.id = p.id ∧ p'.effect = p.effect := by
  simp only [Cedar.TPE.Policy.sliceForRequestEnv] at h
  split at h
  · simp at h
  · simp only [bind, Option.bind] at h
    cases ha : Cedar.TPE.ActionScope.sliceForAction
        p.actionScope env.reqty.action env.acts with
    | none => simp [ha] at h
    | some actionScope =>
      simp only [ha] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq] at h
        subst p'
        exact ⟨rfl, rfl⟩

/-- Slicing policies within one validated request environment only removes
    literal-false residual policies. -/
theorem isAuthorized_with_sliced_policies_refines
    {schema : Schema} {policies : Policies} {req : PartialRequest}
    {es : PartialEntities} {env : TypeEnv} {rf : Cedar.TPE.Response}
    (hreq : validatePartialRequest schema req = .ok env)
    (hents : entitiesIsValid schema es = true)
    (hanc : (es.ancestors req.action).isSome = true)
    (hbase : isAuthorized schema policies req es = .ok rf) :
    ∃ rs,
      isAuthorized schema
        (slicePoliciesForRequestEnv policies env) req es = .ok rs ∧
      rs.SliceRefines rf := by
  apply isAuthorized_refines_of_policy_slice
    (Cedar.TPE.Policy.sliceForRequestEnv · env) ?_ ?_ hbase
  · intro p rp hslice heval
    unfold evalResidualPolicy at heval
    cases hp : evaluatePolicy schema p req es with
    | error e => simp [hp, bind, Except.bind] at heval
    | ok residual =>
      simp only [hp, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at heval
      subst rp
      exact SlicedPoliciesDropped.evaluatePolicy_dropped_isFalse
        hreq hanc hslice hp
  · intro p p' rp hslice heval
    unfold evalResidualPolicy at heval ⊢
    cases hp : evaluatePolicy schema p req es with
    | error e => simp [hp, bind, Except.bind] at heval
    | ok residual =>
      simp only [hp, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at heval
      subst rp
      obtain ⟨hid, heffect⟩ := sliceForRequestEnv_preserves_id_effect hslice
      rw [evaluatePolicy_slice_keep_same_schema hreq hents hanc hslice hp]
      simp only [bind, Except.bind, pure, Except.pure,
        hid, heffect]

end Cedar.Thm
