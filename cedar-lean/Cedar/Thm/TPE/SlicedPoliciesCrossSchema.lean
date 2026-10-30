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

import Cedar.Thm.TPE.SlicedPoliciesCore
import Cedar.Thm.Validation.EnvironmentValidation

/-!
Cross-schema lemmas for `isAuthorizedPartialWithSlicedPolicies`: relating TPE
evaluation under a full schema to evaluation under its action slice
(`Schema.IsActionSliceOf`).
-/

namespace Cedar.Thm.CrossSchema

set_option linter.unusedSectionVars false

open Cedar.Data
open Cedar.Spec
open Cedar.TPE
open Cedar.Validation

/-! ## 1. Action lookup agreement on the closure -/

section ActionLookup

variable {sliced full : Schema} {a : EntityUID}

theorem actionClosure_contains_iff {s : Schema} {u : EntityUID} :
    (s.actionClosure a).contains u = true ↔
      ∃ e, s.acts.find? a = some e ∧ (u = a ∨ u ∈ e.ancestors) := by
  unfold Schema.actionClosure
  cases h : s.acts.find? a with
  | none =>
    simp only [reduceCtorEq, false_and, exists_false, iff_false, Bool.not_eq_true]
    cases hc : (Set.empty : Set EntityUID).contains u
    · rfl
    · have := (Set.contains_prop_bool_equiv).mp hc
      exact absurd this (Set.not_mem_empty u)
  | some e =>
    rw [Set.contains_prop_bool_equiv, Set.mem_make]
    simp only [List.mem_cons, Option.some.injEq, exists_eq_left']
    constructor
    · rintro (h | h)
      · exact .inl h
      · exact .inr ((Set.mem_elts_iff_mem_set _ _).mp h)
    · rintro (h | h)
      · exact .inl h
      · exact .inr ((Set.mem_elts_iff_mem_set _ _).mpr h)

theorem _root_.Cedar.Validation.Schema.IsActionSliceOf.find?_closure (h : sliced.IsActionSliceOf full a) {u : EntityUID}
    (hu : (full.actionClosure a).contains u = true) :
    sliced.acts.find? u = full.acts.find? u := by
  rw [h.acts u]; simp [hu]

theorem _root_.Cedar.Validation.Schema.IsActionSliceOf.find?_some (h : sliced.IsActionSliceOf full a) {u : EntityUID}
    {e : ActionSchemaEntry} (hs : sliced.acts.find? u = some e) :
    full.acts.find? u = some e ∧ (full.actionClosure a).contains u = true := by
  rw [h.acts u] at hs
  split at hs
  · exact ⟨hs, by assumption⟩
  · cases hs

theorem _root_.Cedar.Validation.Schema.IsActionSliceOf.contains_imp (h : sliced.IsActionSliceOf full a) {u : EntityUID}
    (hs : sliced.acts.contains u = true) : full.acts.contains u = true := by
  simp only [ActionSchema.contains, Option.isSome_iff_exists] at hs ⊢
  obtain ⟨e, he⟩ := hs
  exact ⟨e, (h.find?_some he).1⟩

theorem _root_.Cedar.Validation.Schema.IsActionSliceOf.contains_closure (h : sliced.IsActionSliceOf full a) {u : EntityUID}
    (hu : (full.actionClosure a).contains u = true) :
    sliced.acts.contains u = full.acts.contains u := by
  simp only [ActionSchema.contains, h.find?_closure hu]

/-- The request action itself always agrees (both present with the same entry,
    or both absent). -/
theorem _root_.Cedar.Validation.Schema.IsActionSliceOf.find?_self (h : sliced.IsActionSliceOf full a) :
    sliced.acts.find? a = full.acts.find? a := by
  cases hf : full.acts.find? a with
  | none =>
    rw [h.acts a]
    split
    · exact hf
    · rfl
  | some e =>
    rw [← hf]
    apply h.find?_closure
    exact actionClosure_contains_iff.mpr ⟨e, hf, .inl rfl⟩

theorem closure_of_descendentOf {s : Schema} {u : EntityUID}
    (hfa : s.acts.contains a = true) (hd : s.acts.descendentOf a u = true) :
    (s.actionClosure a).contains u = true := by
  simp only [ActionSchema.contains, Option.isSome_iff_exists] at hfa
  obtain ⟨e, he⟩ := hfa
  apply actionClosure_contains_iff.mpr
  refine ⟨e, he, ?_⟩
  simp only [ActionSchema.descendentOf] at hd
  split at hd
  · rename_i heq; exact .inl (beq_iff_eq.mp heq).symm
  · simp only [he] at hd
    exact .inr ((Set.contains_prop_bool_equiv).mp hd)

theorem _root_.Cedar.Validation.Schema.IsActionSliceOf.descendentOf_eq (h : sliced.IsActionSliceOf full a) (u : EntityUID) :
    sliced.acts.descendentOf a u = full.acts.descendentOf a u := by
  simp only [ActionSchema.descendentOf, h.find?_self]

/-- An off-closure action is absent from the slice. -/
theorem _root_.Cedar.Validation.Schema.IsActionSliceOf.find?_off (h : sliced.IsActionSliceOf full a) {u : EntityUID}
    (hu : (full.actionClosure a).contains u = false) : sliced.acts.find? u = none := by
  rw [h.acts u]; simp [hu]

end ActionLookup

/-! ## Well-formedness facts -/

theorem wf_of_environment {s : Schema} {p r : EntityType} {a : EntityUID} {env : TypeEnv}
    (hwf : s.validateWellFormed = .ok ()) (henv : s.environment? p r a = some env) :
    TypeEnv.WellFormed env := by
  apply env_validate_well_formed_is_sound
  exact List.forM_ok_implies_all_ok _ _ hwf env (environment_some_mem_environments henv)

/-! ## 2. `validatePartialRequest` / environment relation -/

section Env

variable {sliced full : Schema} {a : EntityUID}

theorem environment?_slice (h : sliced.IsActionSliceOf full a) (p r : EntityType) :
    sliced.environment? p r a =
      (full.environment? p r a).map (fun env => { env with acts := sliced.acts }) := by
  simp only [Schema.environment?, h.find?_self, h.ets]
  cases full.acts.find? a with
  | none => rfl
  | some ase =>
    simp only [bind, Option.bind]
    cases ase.appliesToPrincipal.contains p <;> cases ase.appliesToResource.contains r <;> rfl

theorem environment?_facts {s : Schema} {p r : EntityType} {a : EntityUID} {env : TypeEnv}
    (h : s.environment? p r a = some env) :
    ∃ ase, s.acts.find? a = some ase ∧ ase.appliesToPrincipal.contains p = true ∧
      ase.appliesToResource.contains r = true ∧
      env = { ets := s.ets, acts := s.acts,
              reqty := { principal := p, action := a, resource := r, context := ase.context } } := by
  simp only [Schema.environment?] at h
  cases hf : s.acts.find? a with
  | none => simp [hf] at h
  | some ase =>
    simp only [hf, bind, Option.bind] at h
    split at h
    · rename_i hp hr
      cases h
      exact ⟨ase, rfl, hp, hr, rfl⟩
    · cases h

theorem validatePartialRequest_environment {s : Schema} {req : PartialRequest} {env : TypeEnv}
    (h : validatePartialRequest s req = .ok env) :
    s.environment? req.principal.ty req.resource.ty req.action = some env ∧
      requestIsValid env req = true := by
  unfold validatePartialRequest at h
  split at h
  · split at h
    · cases h; exact ⟨by assumption, by assumption⟩
    · cases h
  · cases h

/-- The sliced request environment is the full one with the action schema
    replaced by the slice. -/
theorem validatePartialRequest_slice_env (h : sliced.IsActionSliceOf full a)
    {req : PartialRequest} {envF envS : TypeEnv} (hact : req.action = a)
    (hF : validatePartialRequest full req = .ok envF)
    (hS : validatePartialRequest sliced req = .ok envS) :
    envS = { envF with acts := sliced.acts } := by
  subst hact
  have hF' := (validatePartialRequest_environment hF).1
  have hS' := (validatePartialRequest_environment hS).1
  rw [environment?_slice h, hF'] at hS'
  simpa using hS'.symm

theorem env_slice_fields {envF envS : TypeEnv} (henv : envS = { envF with acts := sliced.acts }) :
    envS.ets = envF.ets ∧ envS.acts = sliced.acts ∧ envS.reqty = envF.reqty := by
  subst henv; exact ⟨rfl, rfl, rfl⟩

end Env

/-! ## 3. `sliceForRequestEnv` agrees on full and sliced environments -/

section Slice

theorem typeEnv_descendentOf_of_ets {env₁ env₂ : TypeEnv} {ety₁ : EntityType} (ety₂ : EntityType)
    (hets : env₁.ets = env₂.ets) (hin : env₁.ets.contains ety₁ = true) :
    env₁.descendentOf ety₁ ety₂ = env₂.descendentOf ety₁ ety₂ := by
  simp only [EntitySchema.contains, Option.isSome_iff_exists] at hin
  obtain ⟨e, he⟩ := hin
  simp only [TypeEnv.descendentOf, ← hets, he]

theorem mayMatchType_of_ets {env₁ env₂ : TypeEnv} {ety : EntityType} (s : Scope)
    (hets : env₁.ets = env₂.ets) (hin : env₁.ets.contains ety = true) :
    Scope.mayMatchType s ety env₁ = Scope.mayMatchType s ety env₂ := by
  cases s <;> simp only [Scope.mayMatchType, typeEnv_descendentOf_of_ets _ hets hin]

theorem sliceForAction_congr {acts₁ acts₂ : ActionSchema} {a : EntityUID} (s : ActionScope)
    (h : ∀ u, acts₁.descendentOf a u = acts₂.descendentOf a u) :
    ActionScope.sliceForAction s a acts₁ = ActionScope.sliceForAction s a acts₂ := by
  cases s with
  | actionScope s => cases s <;> simp only [ActionScope.sliceForAction, h]
  | actionInAny uids =>
    simp only [ActionScope.sliceForAction]
    have : uids.filter (acts₁.descendentOf a ·) = uids.filter (acts₂.descendentOf a ·) := by
      congr 1; funext u; exact h u
    rw [this]

theorem sliceForRequestEnv_congr {env₁ env₂ : TypeEnv} (p : Policy)
    (hets : env₁.ets = env₂.ets) (hreqty : env₁.reqty = env₂.reqty)
    (hp : env₁.ets.contains env₁.reqty.principal = true)
    (hr : env₁.ets.contains env₁.reqty.resource = true)
    (hd : ∀ u, env₁.acts.descendentOf env₁.reqty.action u =
      env₂.acts.descendentOf env₁.reqty.action u) :
    Policy.sliceForRequestEnv p env₁ = Policy.sliceForRequestEnv p env₂ := by
  simp only [Policy.sliceForRequestEnv]
  rw [mayMatchType_of_ets _ hets hp, mayMatchType_of_ets _ hets hr,
    sliceForAction_congr _ hd, hreqty]

/-- Under `noActionTypedAttrs`, the principal and resource types of every
    environment are declared entity types. -/
theorem env_principal_resource_ets {s : Schema} {req : PartialRequest} {env : TypeEnv}
    (hno : s.noActionTypedAttrs = true) (h : validatePartialRequest s req = .ok env) :
    env.ets.contains env.reqty.principal = true ∧ env.ets.contains env.reqty.resource = true := by
  obtain ⟨ase, hf, hp, hr, rfl⟩ := environment?_facts (validatePartialRequest_environment h).1
  simp only [Schema.noActionTypedAttrs, Bool.and_eq_true, List.all_eq_true] at hno
  have hval : ase ∈ s.acts.values := Map.in_list_in_values (Map.find?_mem_toList hf)
  obtain ⟨⟨_, hpOk⟩, hrOk⟩ := hno.2 ase hval
  exact ⟨hpOk _ ((Set.mem_elts_iff_mem_set _ _).mpr ((Set.contains_prop_bool_equiv).mp hp)),
    hrOk _ ((Set.mem_elts_iff_mem_set _ _).mpr ((Set.contains_prop_bool_equiv).mp hr))⟩

theorem sliceForRequestEnv_full_eq_sliced {sliced full : Schema} {req : PartialRequest}
    {envF envS : TypeEnv}
    (hslice : sliced.IsActionSliceOf full req.action)
    (hno : full.noActionTypedAttrs = true)
    (hF : validatePartialRequest full req = .ok envF)
    (hS : validatePartialRequest sliced req = .ok envS) (p : Policy) :
    Policy.sliceForRequestEnv p envF = Policy.sliceForRequestEnv p envS := by
  have henv := validatePartialRequest_slice_env hslice rfl hF hS
  obtain ⟨hp, hr⟩ := env_principal_resource_ets hno hF
  obtain ⟨_, _, _, hactF⟩ := SlicedPoliciesActionInAny.env_facts hF
  subst henv
  refine sliceForRequestEnv_congr (env₂ := { envF with acts := sliced.acts }) p rfl rfl hp hr ?_
  intro u
  simp only [hactF, hslice.descendentOf_eq]

end Slice

/-! ## 4. `checkEntities` transfer -/

section CheckEntities

def LitOk (s : Schema) (uid : EntityUID) : Bool :=
  s.ets.isValidEntityUID uid || s.acts.contains uid

def TyOk (s : Schema) (ety : EntityType) : Bool :=
  s.ets.contains ety || s.acts.actionType? ety

theorem forall_mem_union' {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α] {P : α → Prop} {a b : Set α}
    (h : ∀ u ∈ a ∪ b, P u) : (∀ u ∈ a, P u) ∧ (∀ u ∈ b, P u) :=
  ⟨fun u hu => h u ((Set.mem_union a b u).mpr (.inl hu)),
   fun u hu => h u ((Set.mem_union a b u).mpr (.inr hu))⟩

theorem forall_mem_mapUnion {α β} [LT α] [StrictLT α] [DecidableLT α] {P : α → Prop}
    {f : β → Set α} {xs : List β} (h : ∀ u ∈ xs.mapUnion f, P u) :
    ∀ x ∈ xs, ∀ u ∈ f x, P u :=
  fun _ hx u hu => h u (List.mem_mem_implies_mem_mapUnion hu hx)

/-- `checkEntities` transfers between schemas when every literal and every
    `is` type of the expression that is accepted by `s₁` is accepted by `s₂`. -/
theorem checkEntities_transfer {s₁ s₂ : Schema} (x : Expr)
    (hl : ∀ u ∈ x.literalUIDs, LitOk s₁ u = true → LitOk s₂ u = true)
    (ht : ∀ e ∈ x.isEntityTypes, TyOk s₁ e = true → TyOk s₂ e = true)
    (h : checkEntities s₁ x = .ok ()) : checkEntities s₂ x = .ok () := by
  match x with
  | .lit (.entityUID uid) =>
    simp only [checkEntities] at h ⊢
    simp only [Expr.literalUIDs] at hl
    have := hl uid ((Set.mem_singleton uid uid).mpr rfl)
    simp only [LitOk] at this
    split at h
    · rw [ite_eq_left (this (by assumption))]
    · cases h
  | .lit (.bool _) | .lit (.int _) | .lit (.string _) | .var _ =>
    simp [checkEntities]
  | .unaryApp (.is ety) x₁ =>
    simp only [checkEntities] at h ⊢
    simp only [Expr.isEntityTypes] at ht
    simp only [Expr.literalUIDs] at hl
    obtain ⟨ht₁, ht₂⟩ := forall_mem_union' ht
    have := ht₁ ety ((Set.mem_singleton ety ety).mpr rfl)
    simp only [TyOk] at this
    split at h
    · rw [ite_eq_left (this (by assumption))]
      exact checkEntities_transfer x₁ hl ht₂ h
    · cases h
  | .unaryApp .not x₁ | .unaryApp .neg x₁ | .unaryApp .isEmpty x₁
  | .unaryApp (.like _) x₁ | .getAttr x₁ _ | .hasAttr x₁ _ | .extHasAttr x₁ _ _ =>
    simp only [checkEntities] at h ⊢
    simp only [Expr.isEntityTypes] at ht
    simp only [Expr.literalUIDs] at hl
    exact checkEntities_transfer x₁ hl ht h
  | .ite x₁ x₂ x₃ =>
    simp only [checkEntities] at h ⊢
    simp only [Expr.isEntityTypes] at ht
    simp only [Expr.literalUIDs] at hl
    obtain ⟨hl₁₂, hl₃⟩ := forall_mem_union' hl
    obtain ⟨hl₁, hl₂⟩ := forall_mem_union' hl₁₂
    obtain ⟨ht₁₂, ht₃⟩ := forall_mem_union' ht
    obtain ⟨ht₁, ht₂⟩ := forall_mem_union' ht₁₂
    cases h₁ : checkEntities s₁ x₁ with
    | error _ => simp [h₁, bind, Except.bind] at h
    | ok _ =>
    simp only [h₁, bind, Except.bind] at h
    cases h₂ : checkEntities s₁ x₂ with
    | error _ => simp [h₂] at h
    | ok _ =>
    simp only [h₂] at h
    rw [checkEntities_transfer x₁ hl₁ ht₁ h₁, checkEntities_transfer x₂ hl₂ ht₂ h₂,
      checkEntities_transfer x₃ hl₃ ht₃ h]
    rfl
  | .and x₁ x₂ | .or x₁ x₂ | .binaryApp _ x₁ x₂ =>
    simp only [checkEntities] at h ⊢
    simp only [Expr.isEntityTypes] at ht
    simp only [Expr.literalUIDs] at hl
    obtain ⟨hl₁, hl₂⟩ := forall_mem_union' hl
    obtain ⟨ht₁, ht₂⟩ := forall_mem_union' ht
    cases h₁ : checkEntities s₁ x₁ with
    | error _ => simp [h₁, bind, Except.bind] at h
    | ok _ =>
    simp only [h₁, bind, Except.bind] at h
    rw [checkEntities_transfer x₁ hl₁ ht₁ h₁, checkEntities_transfer x₂ hl₂ ht₂ h]
    rfl
  | .set xs | .call _ xs =>
    simp only [checkEntities] at h ⊢
    simp only [Expr.isEntityTypes, List.mapUnion₁_eq_mapUnion Expr.isEntityTypes] at ht
    simp only [Expr.literalUIDs, List.mapUnion₁_eq_mapUnion Expr.literalUIDs] at hl
    have hall := List.forM_ok_implies_all_ok _ _ h
    apply List.all_ok_implies_forM_ok
    intro ⟨y, hy⟩ hmem
    exact checkEntities_transfer y (forall_mem_mapUnion hl y hy) (forall_mem_mapUnion ht y hy)
      (hall ⟨y, hy⟩ hmem)
  | .record axs =>
    simp only [checkEntities] at h ⊢
    simp only [Expr.isEntityTypes,
      List.mapUnion₂_eq_mapUnion (fun x : Attr × Expr => x.snd.isEntityTypes)] at ht
    simp only [Expr.literalUIDs,
      List.mapUnion₂_eq_mapUnion (fun x : Attr × Expr => x.snd.literalUIDs)] at hl
    have hall := List.forM_ok_implies_all_ok _ _ h
    apply List.all_ok_implies_forM_ok
    intro ⟨⟨k, y⟩, hsz⟩ hmem
    have hy := List.mem_attach₂ hmem
    simp only at hy
    have : sizeOf y < sizeOf (Expr.record axs) := by
      simp only [Expr.record.sizeOf_spec]
      simp only at hsz
      omega
    exact checkEntities_transfer y
      (forall_mem_mapUnion (f := fun x : Attr × Expr => x.snd.literalUIDs) hl (k, y) hy)
      (forall_mem_mapUnion (f := fun x : Attr × Expr => x.snd.isEntityTypes) ht (k, y) hy)
      (hall ⟨(k, y), hsz⟩ hmem)
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hy; omega)

/-- Every literal of an expression accepted by `checkEntities` is declared. -/
theorem checkEntities_lits {s : Schema} (x : Expr) (h : checkEntities s x = .ok ()) :
    ∀ u ∈ x.literalUIDs, LitOk s u = true := by
  match x with
  | .lit (.entityUID uid) =>
    simp only [checkEntities] at h
    intro u hu
    simp only [Expr.literalUIDs, Set.mem_singleton] at hu
    subst hu
    split at h
    · rename_i hv; exact hv
    · cases h
  | .lit (.bool _) | .lit (.int _) | .lit (.string _) | .var _ =>
    intro u hu; simp [Expr.literalUIDs, Set.not_mem_empty] at hu
  | .unaryApp (.is ety) x₁ =>
    simp only [checkEntities] at h
    simp only [Expr.literalUIDs]
    split at h
    · exact checkEntities_lits x₁ h
    · cases h
  | .unaryApp .not x₁ | .unaryApp .neg x₁ | .unaryApp .isEmpty x₁
  | .unaryApp (.like _) x₁ | .getAttr x₁ _ | .hasAttr x₁ _ | .extHasAttr x₁ _ _ =>
    simp only [checkEntities] at h
    simp only [Expr.literalUIDs]
    exact checkEntities_lits x₁ h
  | .ite x₁ x₂ x₃ =>
    simp only [checkEntities] at h
    cases h₁ : checkEntities s x₁ with
    | error _ => simp [h₁, bind, Except.bind] at h
    | ok _ =>
    simp only [h₁, bind, Except.bind] at h
    cases h₂ : checkEntities s x₂ with
    | error _ => simp [h₂] at h
    | ok _ =>
    simp only [h₂] at h
    intro u hu
    simp only [Expr.literalUIDs, Set.mem_union] at hu
    rcases hu with (hu | hu) | hu
    · exact checkEntities_lits x₁ h₁ u hu
    · exact checkEntities_lits x₂ h₂ u hu
    · exact checkEntities_lits x₃ h u hu
  | .and x₁ x₂ | .or x₁ x₂ | .binaryApp _ x₁ x₂ =>
    simp only [checkEntities] at h
    cases h₁ : checkEntities s x₁ with
    | error _ => simp [h₁, bind, Except.bind] at h
    | ok _ =>
    simp only [h₁, bind, Except.bind] at h
    intro u hu
    simp only [Expr.literalUIDs, Set.mem_union] at hu
    rcases hu with hu | hu
    · exact checkEntities_lits x₁ h₁ u hu
    · exact checkEntities_lits x₂ h u hu
  | .set xs | .call _ xs =>
    simp only [checkEntities] at h
    have hall := List.forM_ok_implies_all_ok _ _ h
    intro u hu
    simp only [Expr.literalUIDs, List.mapUnion₁_eq_mapUnion Expr.literalUIDs] at hu
    obtain ⟨y, hy, huy⟩ := (List.mem_mapUnion_iff_mem_exists u).mp hu
    exact checkEntities_lits y (hall ⟨y, hy⟩ (List.mem_attach _ _)) u huy
  | .record axs =>
    simp only [checkEntities] at h
    have hall := List.forM_ok_implies_all_ok _ _ h
    intro u hu
    simp only [Expr.literalUIDs,
      List.mapUnion₂_eq_mapUnion (fun x : Attr × Expr => x.snd.literalUIDs)] at hu
    obtain ⟨⟨k, y⟩, hy, huy⟩ := (List.mem_mapUnion_iff_mem_exists u).mp hu
    have hsz : sizeOf (k, y).snd < 1 + sizeOf axs := by
      have h₁ := List.sizeOf_lt_of_mem hy
      simp only [Prod.mk.sizeOf_spec] at h₁ ⊢
      omega
    have hmem : (⟨(k, y), hsz⟩ : {x : Attr × Expr // sizeOf x.snd < 1 + sizeOf axs}) ∈ axs.attach₂ := by
      simp only [List.attach₂, List.mem_pmap]
      exact ⟨(k, y), hy, rfl⟩
    have : sizeOf y < sizeOf (Expr.record axs) := by
      simp only [Expr.record.sizeOf_spec]; simp only at hsz; omega
    exact checkEntities_lits y (hall _ hmem) u huy
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hy; omega)

/-- Membership in a function of `Conditions.toExpr` for any "and-additive"
    expression measure (`literalUIDs`, `isEntityTypes`). -/
theorem mem_conditions_toExpr {α} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α]
    (f : Expr → Set α)
    (hand : ∀ x y, f (.and x y) = f x ∪ f y) (hnot : ∀ x, f (.unaryApp .not x) = f x)
    (htrue : ∀ u, u ∉ f (.lit (.bool true)))
    {u : α} {cs : Conditions} (hu : u ∈ f cs.toExpr) : ∃ c ∈ cs, u ∈ f c.body := by
  have hc : ∀ c : Condition, f c.toExpr = f c.body := by
    intro c; unfold Condition.toExpr; cases c.kind <;> simp [hnot]
  have hfold : ∀ (l : List Condition) (acc : Expr),
      u ∈ f (l.foldl (λ e c => .and c.toExpr e) acc) → u ∈ f acc ∨ ∃ c ∈ l, u ∈ f c.body := by
    intro l
    induction l with
    | nil => intro acc h; exact .inl h
    | cons c l ih =>
      intro acc h
      simp only [List.foldl_cons] at h
      rcases ih _ h with h | ⟨c', hc', h⟩
      · rw [hand, Set.mem_union, hc] at h
        rcases h with h | h
        · exact .inr ⟨c, List.mem_cons_self .., h⟩
        · exact .inl h
      · exact .inr ⟨c', List.mem_cons_of_mem _ hc', h⟩
  unfold Conditions.toExpr at hu
  split at hu
  · exact absurd hu (htrue u)
  · rename_i c cs' hrev
    rcases hfold cs' _ hu with h | ⟨c', hc', h⟩
    · rw [hc] at h
      refine ⟨c, ?_, h⟩
      have : c ∈ cs.reverse := by rw [hrev]; exact List.mem_cons_self ..
      exact List.mem_reverse.mp this
    · refine ⟨c', ?_, h⟩
      have : c' ∈ cs.reverse := by rw [hrev]; exact List.mem_cons_of_mem _ hc'
      exact List.mem_reverse.mp this

theorem mem_conditions_literalUIDs {u : EntityUID} {cs : Conditions}
    (hu : u ∈ cs.toExpr.literalUIDs) : ∃ c ∈ cs, u ∈ c.body.literalUIDs :=
  mem_conditions_toExpr Expr.literalUIDs (by intros; simp [Expr.literalUIDs])
    (by intros; simp [Expr.literalUIDs]) (by intro u; simp [Expr.literalUIDs, Set.not_mem_empty]) hu

theorem mem_conditions_isEntityTypes {e : EntityType} {cs : Conditions}
    (hu : e ∈ cs.toExpr.isEntityTypes) : ∃ c ∈ cs, e ∈ c.body.isEntityTypes :=
  mem_conditions_toExpr Expr.isEntityTypes (by intros; simp [Expr.isEntityTypes])
    (by intros; simp [Expr.isEntityTypes]) (by intro u; simp [Expr.isEntityTypes, Set.not_mem_empty]) hu

theorem scope_literalUIDs {sc : Scope} {v : Var} {u : EntityUID}
    (hu : u ∈ (sc.toExpr v).literalUIDs) : sc.bound = some u := by
  cases sc <;>
    simp [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType, Expr.literalUIDs,
      Set.mem_union, Set.mem_singleton, Set.not_mem_empty, Scope.bound] at hu ⊢
  all_goals exact hu.symm

theorem scope_isEntityTypes {sc : Scope} {v : Var} {e : EntityType}
    (he : e ∈ (sc.toExpr v).isEntityTypes) :
    sc = .is e ∨ ∃ uid, sc = .isMem e uid := by
  cases sc <;>
    simp [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType, Expr.isEntityTypes,
      Set.mem_union, Set.mem_singleton, Set.not_mem_empty] at he ⊢
  all_goals subst he; rfl

theorem policy_literalUIDs {p : Policy} {u : EntityUID} (hu : u ∈ p.toExpr.literalUIDs) :
    u ∈ p.principalScope.toExpr.literalUIDs ∨ u ∈ p.actionScope.toExpr.literalUIDs ∨
    u ∈ p.resourceScope.toExpr.literalUIDs ∨ u ∈ p.condition.toExpr.literalUIDs := by
  simpa [Policy.toExpr, Expr.literalUIDs, Set.mem_union] using hu

theorem policy_isEntityTypes {p : Policy} {e : EntityType} (he : e ∈ p.toExpr.isEntityTypes) :
    e ∈ p.principalScope.toExpr.isEntityTypes ∨ e ∈ p.actionScope.toExpr.isEntityTypes ∨
    e ∈ p.resourceScope.toExpr.isEntityTypes ∨ e ∈ p.condition.toExpr.isEntityTypes := by
  simpa [Policy.toExpr, Expr.isEntityTypes, Set.mem_union] using he

end CheckEntities

/-! ## 4b. `checkEntities` for a kept policy under the sliced schema -/

section CheckSliced

theorem lits_literalUIDs {us : List EntityUID} {u : EntityUID}
    (hu : u ∈ (us.map fun e => Expr.lit (.entityUID e)).mapUnion₁ (fun x => x.val.literalUIDs)) :
    u ∈ us := by
  simp only [List.mapUnion₁_eq_mapUnion Expr.literalUIDs] at hu
  obtain ⟨x, hx, hux⟩ := (List.mem_mapUnion_iff_mem_exists u).mp hu
  obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hx
  simp only [Expr.literalUIDs, Set.mem_singleton] at hux
  subst hux; exact hu'

theorem lits_isEntityTypes {us : List EntityUID} {e : EntityType}
    (he : e ∈ (us.map fun e => Expr.lit (.entityUID e)).mapUnion₁ (fun x => x.val.isEntityTypes)) :
    False := by
  simp only [List.mapUnion₁_eq_mapUnion Expr.isEntityTypes] at he
  obtain ⟨x, hx, hex⟩ := (List.mem_mapUnion_iff_mem_exists e).mp he
  obtain ⟨u', _, rfl⟩ := List.mem_map.mp hx
  simp [Expr.isEntityTypes, Set.not_mem_empty] at hex

/-- Literals and `is` types of a sliced action scope are in the request
    action's closure / are the request action's type. -/
theorem sliceForAction_facts {s s' : ActionScope} {a : EntityUID} {acts : ActionSchema}
    (h : ActionScope.sliceForAction s a acts = some s') :
    (∀ u ∈ s'.toExpr.literalUIDs, acts.descendentOf a u = true) ∧
    (∀ e ∈ s'.toExpr.isEntityTypes, e = a.ty) := by
  cases s with
  | actionScope sc =>
    cases sc <;> simp only [ActionScope.sliceForAction] at h
    all_goals (repeat' split at h) <;> (try cases h)
    all_goals constructor
    all_goals intro x hx
    all_goals
      simp [ActionScope.toExpr, Scope.toExpr, Var.eqEntityUID, Var.inEntityUID,
        Var.isEntityType, Expr.literalUIDs, Expr.isEntityTypes, Set.mem_union,
        Set.mem_singleton, Set.not_mem_empty] at hx
    all_goals (try subst hx)
    all_goals simp_all [ActionSchema.descendentOf]
  | actionInAny uids =>
    simp only [ActionScope.sliceForAction] at h
    split at h
    · cases h
    · cases h
      constructor
      · intro u hu
        simp only [ActionScope.toExpr, Expr.literalUIDs, Set.mem_union] at hu
        rcases hu with hu | hu
        · simp [Set.not_mem_empty] at hu
        · have := lits_literalUIDs hu
          exact (List.mem_filter.mp this).2
      · intro e he
        simp only [ActionScope.toExpr, Expr.isEntityTypes, Set.mem_union] at he
        rcases he with he | he
        · simp [Set.not_mem_empty] at he
        · exact (lits_isEntityTypes he).elim

theorem sliceForAction_cases {s s' : ActionScope} {a : EntityUID} {acts : ActionSchema}
    (h : ActionScope.sliceForAction s a acts = some s') :
    s' = s ∨ ∃ uids, s = .actionInAny uids ∧
      s' = .actionInAny (uids.filter (acts.descendentOf a ·)) := by
  cases s with
  | actionScope sc =>
    left
    cases sc <;> simp only [ActionScope.sliceForAction] at h
    all_goals (repeat' split at h) <;> (try cases h)
    all_goals rfl
  | actionInAny uids =>
    right
    simp only [ActionScope.sliceForAction] at h
    split at h
    · cases h
    · cases h; exact ⟨uids, rfl, rfl⟩

theorem sliceForRequestEnv_facts {p p' : Policy} {env : TypeEnv}
    (h : Policy.sliceForRequestEnv p env = some p') :
    Scope.mayMatchType p.principalScope.scope env.reqty.principal env = true ∧
    Scope.mayMatchType p.resourceScope.scope env.reqty.resource env = true ∧
    ∃ as', ActionScope.sliceForAction p.actionScope env.reqty.action env.acts = some as' ∧
      p' = { p with actionScope := as' } := by
  simp only [Policy.sliceForRequestEnv] at h
  split at h
  · cases h
  · rename_i hp
    simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i as' has
      split at h
      · cases h
      · rename_i hr
        cases h
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hp hr
        exact ⟨by simpa using hp, by simpa using hr, as', has, rfl⟩

/-- In a well-formed environment, `descendentOf` from a declared entity type
    only reaches declared entity types. -/
theorem descendentOf_ets {env : TypeEnv} (hwf : TypeEnv.WellFormed env) {ety₁ ety₂ : EntityType}
    (h₁ : env.ets.contains ety₁ = true) (hd : env.descendentOf ety₁ ety₂ = true) :
    env.ets.contains ety₂ = true := by
  simp only [TypeEnv.descendentOf] at hd
  split at hd
  · rename_i heq; subst heq; exact h₁
  · simp only [EntitySchema.contains, Option.isSome_iff_exists] at h₁
    obtain ⟨entry, he⟩ := h₁
    simp only [he] at hd
    have hentry := hwf.1.2 _ _ he
    cases entry with
    | enum es =>
      simp [EntitySchemaEntry.ancestors] at hd
      exact absurd hd (Set.not_mem_empty _)
    | standard se =>
      simp only [EntitySchemaEntry.ancestors] at hd
      obtain ⟨e', he'⟩ := hentry.2.1 ety₂ ((Set.contains_prop_bool_equiv).mp hd)
      simp [EntitySchema.contains, he']

/-- Literals and `is` types of a principal/resource scope that may match a
    declared entity type are themselves declared entity types. -/
theorem scope_types_ets {env : TypeEnv} (hwf : TypeEnv.WellFormed env) {sc : Scope}
    {ety : EntityType} {v : Var} (hety : env.ets.contains ety = true)
    (hm : Scope.mayMatchType sc ety env = true) :
    (∀ u ∈ (sc.toExpr v).literalUIDs, env.ets.contains u.ty = true) ∧
    (∀ e ∈ (sc.toExpr v).isEntityTypes, env.ets.contains e = true) := by
  constructor
  · intro u hu
    have hb := scope_literalUIDs hu
    cases sc <;> simp only [Scope.bound, Option.some.injEq, reduceCtorEq] at hb <;> subst hb <;>
      simp only [Scope.mayMatchType, Bool.and_eq_true, beq_iff_eq] at hm
    · subst hm; exact hety
    · exact descendentOf_ets hwf hety hm
    · exact descendentOf_ets hwf hety hm.2
  · intro e he
    rcases scope_isEntityTypes he with rfl | ⟨uid, rfl⟩ <;>
      simp only [Scope.mayMatchType, Bool.and_eq_true, beq_iff_eq] at hm
    · subst hm; exact hety
    · rw [← hm.1]; exact hety

theorem litOk_of_ets {s₁ s₂ : Schema} {u : EntityUID} (hets : s₂.ets = s₁.ets)
    (hdisj : ∀ u, s₁.acts.contains u = true → ¬ s₁.ets.contains u.ty = true)
    (hu : s₁.ets.contains u.ty = true) (h : LitOk s₁ u = true) : LitOk s₂ u = true := by
  simp only [LitOk, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact .inl (hets ▸ h)
  · exact absurd hu (hdisj u h)

theorem litOk_of_closure {sliced full : Schema} {a u : EntityUID}
    (hslice : sliced.IsActionSliceOf full a) (hu : (full.actionClosure a).contains u = true)
    (h : LitOk full u = true) : LitOk sliced u = true := by
  simp only [LitOk, hslice.ets, hslice.contains_closure hu] at h ⊢
  exact h

theorem litOk_of_nonaction {s₁ s₂ : Schema} {u : EntityUID} (hets : s₂.ets = s₁.ets)
    (hna : s₁.acts.actionType? u.ty = false) (h : LitOk s₁ u = true) : LitOk s₂ u = true := by
  simp only [LitOk, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact .inl (hets ▸ h)
  · rw [actionType?_of_contains h] at hna; cases hna

theorem tyOk_of_ets {s₁ s₂ : Schema} {e : EntityType} (hets : s₂.ets = s₁.ets)
    (he : s₁.ets.contains e = true) : TyOk s₂ e = true := by
  simp [TyOk, hets, he]

theorem tyOk_of_nonaction {s₁ s₂ : Schema} {e : EntityType} (hets : s₂.ets = s₁.ets)
    (hna : s₁.acts.actionType? e = false) (h : TyOk s₁ e = true) : TyOk s₂ e = true := by
  simp only [TyOk, hna, Bool.or_false] at h
  exact tyOk_of_ets hets h

/-- `checkEntities` succeeds under the sliced schema for the sliced policy. -/
theorem checkEntities_sliced_policy {sliced full : Schema} {req : PartialRequest}
    {envF : TypeEnv} {policies : Policies} {p p' : Policy}
    (hslice : sliced.IsActionSliceOf full req.action)
    (hwf : full.validateWellFormed = .ok ())
    (hmem : p ∈ policies)
    (hnolits : full.noActionLiteralsInConditions policies = true)
    (hnotests : full.noActionTypeTestsInConditions policies = true)
    (hno : full.noActionTypedAttrs = true)
    (hF : validatePartialRequest full req = .ok envF)
    (hsl : Policy.sliceForRequestEnv p envF = some p')
    (hcheck : checkEntities full p.toExpr = .ok ()) :
    checkEntities sliced p'.toExpr = .ok () := by
  have hwfenv := wf_of_environment hwf (validatePartialRequest_environment hF).1
  obtain ⟨ase, hfind, hets, hacts, hact⟩ := SlicedPoliciesActionInAny.env_facts hF
  have hdisj : ∀ u, full.acts.contains u = true → ¬ full.ets.contains u.ty = true := by
    have := hwfenv.2.1.2.2.1
    rw [hets, hacts] at this
    exact this
  obtain ⟨hpc, hrc⟩ := env_principal_resource_ets hno hF
  obtain ⟨hpm, hrm, as', has, rfl⟩ := sliceForRequestEnv_facts hsl
  rw [hact, hacts] at has
  -- Step 1: the sliced policy passes `checkEntities` under the full schema.
  have hcheck' : checkEntities full ({ p with actionScope := as' } : Policy).toExpr = .ok () := by
    rw [SlicedPoliciesActionInAny.policy_toExpr_check] at hcheck ⊢
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hcheck
    refine ⟨h₁, ?_, h₃, h₄⟩
    rcases sliceForAction_cases has with rfl | ⟨uids, huids, rfl⟩
    · exact h₂
    · rw [huids] at h₂
      exact SlicedPoliciesActionInAny.check_actionInAny (fun u hu => (List.mem_filter.mp hu).1) h₂
  -- Step 2: transfer to the sliced schema.
  have hfa : full.acts.contains req.action = true := by
    simp [ActionSchema.contains, hfind]
  obtain ⟨hasL, hasT⟩ := sliceForAction_facts has
  have hcondL : ∀ u ∈ p.condition.toExpr.literalUIDs, full.acts.actionType? u.ty = false := by
    intro u hu
    obtain ⟨c, hc, hu⟩ := mem_conditions_literalUIDs hu
    simp only [Schema.noActionLiteralsInConditions, List.all_eq_true, Bool.not_eq_true'] at hnolits
    exact hnolits p hmem u ((Set.mem_elts_iff_mem_set _ _).mpr
      (List.mem_mem_implies_mem_mapUnion (f := fun c : Condition => c.body.literalUIDs) hu hc))
  have hcondT : ∀ e ∈ p.condition.toExpr.isEntityTypes, full.acts.actionType? e = false := by
    intro e he
    obtain ⟨c, hc, he⟩ := mem_conditions_isEntityTypes he
    simp only [Schema.noActionTypeTestsInConditions, List.all_eq_true, Bool.not_eq_true'] at hnotests
    exact hnotests p hmem e ((Set.mem_elts_iff_mem_set _ _).mpr
      (List.mem_mem_implies_mem_mapUnion (f := fun c : Condition => c.body.isEntityTypes) he hc))
  rw [hets] at hpc hrc
  have hpm' : Scope.mayMatchType p.principalScope.scope envF.reqty.principal envF = true := hpm
  have hrm' : Scope.mayMatchType p.resourceScope.scope envF.reqty.resource envF = true := hrm
  have hpS := scope_types_ets (v := .principal) hwfenv (hets ▸ hpc) hpm'
  have hrS := scope_types_ets (v := .resource) hwfenv (hets ▸ hrc) hrm'
  rw [hets] at hpS hrS
  have hpe : p.principalScope.toExpr = p.principalScope.scope.toExpr .principal := by
    cases p.principalScope; rfl
  have hre : p.resourceScope.toExpr = p.resourceScope.scope.toExpr .resource := by
    cases p.resourceScope; rfl
  apply checkEntities_transfer _ _ _ hcheck'
  · intro u hu hok
    rcases policy_literalUIDs hu with hu | hu | hu | hu
    · rw [hpe] at hu
      exact litOk_of_ets hslice.ets hdisj (hpS.1 u hu) hok
    · exact litOk_of_closure hslice (closure_of_descendentOf hfa (hasL u hu)) hok
    · rw [hre] at hu
      exact litOk_of_ets hslice.ets hdisj (hrS.1 u hu) hok
    · exact litOk_of_nonaction hslice.ets (hcondL u hu) hok
  · intro e he hok
    rcases policy_isEntityTypes he with he | he | he | he
    · rw [hpe] at he
      exact tyOk_of_ets hslice.ets (hpS.2 e he)
    · rw [hasT e he]
      have : sliced.acts.contains req.action = true := by
        simp [ActionSchema.contains, hslice.find?_self, hfind]
      simp [TyOk, actionType?_of_contains this]
    · rw [hre] at he
      exact tyOk_of_ets hslice.ets (hrS.2 e he)
    · exact tyOk_of_nonaction hslice.ets (hcondT e he) hok

end CheckSliced

/-! ## 5a. Entity-type invariants on `CedarType` -/

section TyInv

theorem entityTypesAll_record_iff {ok : EntityType → Bool} {rty : RecordType} :
    (CedarType.record rty).entityTypesAll ok = true ↔
      ∀ kq ∈ rty.toList, kq.2.getType.entityTypesAll ok = true := by
  rw [CedarType.entityTypesAll]
  simp only [List.all_eq_true]
  constructor
  · intro h kq hkq
    have := h ⟨kq, hkq⟩ (List.mem_attach _ _)
    obtain ⟨k, q⟩ := kq
    cases q <;> simpa [Qualified.getType] using this
  · intro h ⟨⟨k, q⟩, hkq⟩ _
    have := h (k, q) hkq
    cases q <;> simpa [Qualified.getType] using this

theorem entityTypesAll_mono {p q : EntityType → Bool} (hpq : ∀ e, p e = true → q e = true) :
    ∀ ty : CedarType, ty.entityTypesAll p = true → ty.entityTypesAll q = true
  | .bool _, _ | .int, _ | .string, _ | .ext _, _ => by simp [CedarType.entityTypesAll]
  | .entity e, h => by simp only [CedarType.entityTypesAll] at h ⊢; exact hpq e h
  | .set ty, h => by
    simp only [CedarType.entityTypesAll] at h ⊢; exact entityTypesAll_mono hpq ty h
  | .record rty, h => by
    rw [entityTypesAll_record_iff] at h ⊢
    intro kq hkq
    have : sizeOf kq.2.getType < sizeOf (CedarType.record rty) := by
      have h₁ := List.sizeOf_lt_of_mem hkq
      have h₂ := Map.sizeOf_lt_of_toList rty
      obtain ⟨k, qt⟩ := kq
      cases qt <;> simp only [Qualified.getType, Prod.mk.sizeOf_spec,
        Qualified.optional.sizeOf_spec, Qualified.required.sizeOf_spec,
        CedarType.record.sizeOf_spec] at h₁ ⊢ <;> omega
    exact entityTypesAll_mono hpq kq.2.getType (h kq hkq)
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (simp only [CedarType.record.sizeOf_spec] at this; omega)

mutual
theorem lub_inv {ok : EntityType → Bool} {ty₁ ty₂ ty₃ : CedarType} :
    (ty₁ ⊔ ty₂) = some ty₃ → ty₁.entityTypesAll ok = true → ty₃.entityTypesAll ok = true := by
  unfold lub?
  intro h₁ h
  split at h₁
  case h_1 => simp at h₁; subst h₁; simp [CedarType.entityTypesAll]
  case h_2 sty₁ sty₂ =>
    cases h₂ : sty₁ ⊔ sty₂ <;> simp [h₂] at h₁
    subst h₁
    simp only [CedarType.entityTypesAll] at h ⊢
    exact lub_inv h₂ h
  case h_3 rty₁ rty₂ =>
    cases h₂ : lubRecordType rty₁ rty₂ <;> simp [h₂] at h₁
    subst h₁
    rw [entityTypesAll_record_iff] at h ⊢
    simp only [Map.toList_mk_id] at h ⊢
    exact lubRecordType_inv h₂ h
  case h_4 =>
    split at h₁
    · simp at h₁; subst h₁; exact h
    · cases h₁

theorem lubRecordType_inv {ok : EntityType → Bool} {rty₁ rty₂ rty₃ : List (Attr × QualifiedType)} :
    lubRecordType rty₁ rty₂ = some rty₃ →
    (∀ kq ∈ rty₁, kq.2.getType.entityTypesAll ok = true) →
    ∀ kq ∈ rty₃, kq.2.getType.entityTypesAll ok = true := by
  unfold lubRecordType
  intro h₁ h
  split at h₁
  case h_1 => simp at h₁; subst h₁; simp
  case h_2 a₁ qty₁ rty₁' a₂ qty₂ rty₂' =>
    split at h₁
    · cases h₁
    · cases h₂ : lubQualifiedType qty₁ qty₂ <;> simp [h₂] at h₁
      rename_i qty₃
      cases h₃ : lubRecordType rty₁' rty₂' <;> simp [h₃] at h₁
      rename_i rty₃'
      subst h₁
      simp only [List.mem_cons, forall_eq_or_imp] at h ⊢
      exact ⟨lubQualifiedType_inv h₂ h.1, lubRecordType_inv h₃ h.2⟩
  case h_3 => cases h₁

theorem lubQualifiedType_inv {ok : EntityType → Bool} {qty₁ qty₂ qty₃ : QualifiedType} :
    lubQualifiedType qty₁ qty₂ = some qty₃ →
    qty₁.getType.entityTypesAll ok = true → qty₃.getType.entityTypesAll ok = true := by
  unfold lubQualifiedType
  intro h₁ h
  split at h₁
  case h_1 aty₁ aty₂ =>
    cases h₂ : aty₁ ⊔ aty₂ <;> simp [h₂] at h₁
    subst h₁
    simp only [Qualified.getType] at h ⊢
    exact lub_inv h₂ h
  case h_2 aty₁ aty₂ =>
    cases h₂ : aty₁ ⊔ aty₂ <;> simp [h₂] at h₁
    subst h₁
    simp only [Qualified.getType] at h ⊢
    exact lub_inv h₂ h
  case h_3 => cases h₁
end

theorem foldlM_lub_inv {ok : EntityType → Bool} :
    ∀ (tys : List CedarType) (acc ty : CedarType),
    tys.foldlM lub? acc = some ty → acc.entityTypesAll ok = true → ty.entityTypesAll ok = true
  | [], acc, ty, h, hacc => by simp at h; subst h; exact hacc
  | t :: ts, acc, ty, h, hacc => by
    simp only [List.foldlM_cons] at h
    cases h₁ : acc ⊔ t with
    | none => simp [h₁] at h
    | some acc' =>
      simp only [h₁, Option.bind_eq_bind, Option.bind_some] at h
      exact foldlM_lub_inv ts acc' ty h (lub_inv h₁ hacc)

end TyInv

/-! ## 5b. Relating the full and sliced type environments -/

/-- Facts relating the full request environment `envF` and the sliced one
    `envS`. All are derivable from the top-level hypotheses
    (see `envRel_of_slice`). -/
structure EnvRel (envF envS : TypeEnv) : Prop where
  ets : envS.ets = envF.ets
  reqty : envS.reqty = envF.reqty
  actF : envF.acts.contains envF.reqty.action = true
  actS : envS.acts.contains envF.reqty.action = true
  sub : ∀ u e, envS.acts.find? u = some e → envF.acts.find? u = some e
  desc : ∀ u, envS.acts.descendentOf envF.reqty.action u = envF.acts.descendentOf envF.reqty.action u
  disj : ∀ u, envF.acts.contains u = true → ¬ envF.ets.contains u.ty = true
  ancActs : ∀ u e, (u, e) ∈ envF.acts.toList → ∀ anc ∈ e.ancestors, envF.acts.contains anc = true
  subList : ∀ u e, (u, e) ∈ envS.acts.toList → (u, e) ∈ envF.acts.toList
  closureContains : ∀ u, envF.acts.descendentOf envF.reqty.action u = true →
    envS.acts.contains u = envF.acts.contains u
  ctx : (CedarType.record envF.reqty.context).entityTypesAll envF.ets.contains = true
  prin : envF.ets.contains envF.reqty.principal = true
  res : envF.ets.contains envF.reqty.resource = true
  attrs : ∀ ety rty, envF.ets.attrs? ety = some rty →
    (CedarType.record rty).entityTypesAll envF.ets.contains = true
  tags : ∀ ety ty, envF.ets.tags? ety = some (some ty) → ty.entityTypesAll envF.ets.contains = true

namespace EnvRel

variable {envF envS : TypeEnv} (h : EnvRel envF envS)
include h

/-- Entity types that can occur in the types of condition subexpressions:
    declared entity types and the request action's type. -/
def S (envF : TypeEnv) (e : EntityType) : Bool :=
  envF.ets.contains e || e == envF.reqty.action.ty

def Inv (envF : TypeEnv) (ty : CedarType) : Prop := ty.entityTypesAll (S envF) = true

/-- Good literals: declared entities, or the request action itself. -/
def GoodLit (envF : TypeEnv) (u : EntityUID) : Prop :=
  envF.ets.isValidEntityUID u = true ∨ u = envF.reqty.action

omit h in
theorem ets_imp_S {e : EntityType} (he : envF.ets.contains e = true) : S envF e = true := by
  simp [S, he]

omit h in
theorem inv_of_ets {ty : CedarType} (hty : ty.entityTypesAll envF.ets.contains = true) :
    Inv envF ty :=
  entityTypesAll_mono (fun _ he => ets_imp_S he) ty hty

theorem contains_S_imp {u : EntityUID} (hc : envS.acts.contains u = true) :
    envF.acts.contains u = true := by
  simp only [ActionSchema.contains, Option.isSome_iff_exists] at hc ⊢
  obtain ⟨e, he⟩ := hc
  exact ⟨e, h.sub u e he⟩

theorem act_ty_not_ets : envF.ets.contains envF.reqty.action.ty = false := by
  cases hc : envF.ets.contains envF.reqty.action.ty
  · rfl
  · exact absurd hc (h.disj _ h.actF)

omit h in
theorem isValid_imp_contains {u : EntityUID} (hv : envF.ets.isValidEntityUID u = true) :
    envF.ets.contains u.ty = true := by
  simp only [EntitySchema.isValidEntityUID] at hv
  simp only [EntitySchema.contains, Option.isSome_iff_exists]
  split at hv
  · rename_i e he; exact ⟨e, he⟩
  · cases hv

theorem contains_agree_good {u : EntityUID} (hu : GoodLit envF u) :
    envS.acts.contains u = envF.acts.contains u := by
  rcases hu with hu | rfl
  · have hF : envF.acts.contains u = false := by
      cases hc : envF.acts.contains u
      · rfl
      · exact absurd (isValid_imp_contains hu) (h.disj u hc)
    have hS : envS.acts.contains u = false := by
      cases hc : envS.acts.contains u
      · rfl
      · rw [h.contains_S_imp hc] at hF; cases hF
    rw [hF, hS]
  · rw [h.actF, h.actS]

theorem good_S {u : EntityUID} (hu : GoodLit envF u) : S envF u.ty = true := by
  rcases hu with hu | rfl
  · exact ets_imp_S (isValid_imp_contains hu)
  · simp [S]

omit h in
theorem maybeDescendentOf_false {acts : ActionSchema} {ets : EntitySchema} {e₁ e₂ : EntityType}
    (hanc : ∀ u e, (u, e) ∈ acts.toList → ∀ anc ∈ e.ancestors, ¬ ets.contains anc.ty = true)
    (he₂ : ets.contains e₂ = true) :
    acts.maybeDescendentOf e₁ e₂ = false := by
  simp only [ActionSchema.maybeDescendentOf, List.any_eq_false]
  intro ⟨act, entry⟩ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Set.any, List.any_eq_true,
    beq_iff_eq, not_exists]
  intro _ anc hanc' hty
  subst hty
  exact hanc act entry hmem anc ((Set.mem_elts_iff_mem_set _ _).mp hanc') he₂

theorem ancF_not_ets : ∀ u e, (u, e) ∈ envF.acts.toList → ∀ anc ∈ e.ancestors,
    ¬ envF.ets.contains anc.ty = true :=
  fun u e hm anc ha => h.disj anc (h.ancActs u e hm anc ha)

theorem ancS_not_ets : ∀ u e, (u, e) ∈ envS.acts.toList → ∀ anc ∈ e.ancestors,
    ¬ envS.ets.contains anc.ty = true := by
  intro u e hm anc ha
  rw [h.ets]
  exact h.ancF_not_ets u e (h.subList u e hm) anc ha

/-- `TypeEnv.descendentOf` agrees on all pairs of types in `S`. -/
theorem descendentOf_agree {e₁ e₂ : EntityType} (h₁ : S envF e₁ = true) (h₂ : S envF e₂ = true) :
    envS.descendentOf e₁ e₂ = envF.descendentOf e₁ e₂ := by
  simp only [TypeEnv.descendentOf, h.ets]
  split
  · rfl
  · rename_i hne
    cases hnone : envF.ets.find? e₁ with
    | some _ => rfl
    | none =>
      simp only
      have he₁ : envF.ets.contains e₁ = false := by
        simp [EntitySchema.contains, hnone]
      simp only [S, he₁, Bool.false_or, beq_iff_eq] at h₁
      subst h₁
      have he₂ : envF.ets.contains e₂ = true := by
        simp only [S, Bool.or_eq_true, beq_iff_eq] at h₂
        rcases h₂ with h₂ | h₂
        · exact h₂
        · exact absurd h₂.symm hne
      rw [maybeDescendentOf_false h.ancF_not_ets he₂,
        maybeDescendentOf_false (h.ets ▸ h.ancS_not_ets) he₂]

theorem actionType?_agree {e : EntityType} (hS : S envF e = true)
    (hnot : envF.ets.contains e = false) :
    envS.acts.actionType? e = envF.acts.actionType? e := by
  simp only [S, hnot, Bool.false_or, beq_iff_eq] at hS
  subst hS
  rw [actionType?_of_contains h.actS, actionType?_of_contains h.actF]

end EnvRel

/-! ## 5c. Typed-expression invariant -/

/-- Every node of a typed expression has a type satisfying `P`. -/
inductive AllTy (P : CedarType → Prop) : TypedExpr → Prop where
  | lit {p ty} : P ty → AllTy P (.lit p ty)
  | var {v ty} : P ty → AllTy P (.var v ty)
  | ite {a b c ty} : AllTy P a → AllTy P b → AllTy P c → P ty → AllTy P (.ite a b c ty)
  | and {a b ty} : AllTy P a → AllTy P b → P ty → AllTy P (.and a b ty)
  | or {a b ty} : AllTy P a → AllTy P b → P ty → AllTy P (.or a b ty)
  | unaryApp {op a ty} : AllTy P a → P ty → AllTy P (.unaryApp op a ty)
  | binaryApp {op a b ty} : AllTy P a → AllTy P b → P ty → AllTy P (.binaryApp op a b ty)
  | getAttr {a attr ty} : AllTy P a → P ty → AllTy P (.getAttr a attr ty)
  | hasAttr {a attr ty} : AllTy P a → P ty → AllTy P (.hasAttr a attr ty)
  | extHasAttr {a attr attrs ty} : AllTy P a → P ty → AllTy P (.extHasAttr a attr attrs ty)
  | set {xs ty} : (∀ x ∈ xs, AllTy P x) → P ty → AllTy P (.set xs ty)
  | record {axs ty} : (∀ ax ∈ axs, AllTy P ax.2) → P ty → AllTy P (.record axs ty)
  | call {xfn xs ty} : (∀ x ∈ xs, AllTy P x) → P ty → AllTy P (.call xfn xs ty)

theorem AllTy.top {P : CedarType → Prop} {t : TypedExpr} (h : AllTy P t) : P t.typeOf := by
  cases h <;> simp_all [TypedExpr.typeOf]

/-! ## 5d. Agreement of the env-sensitive typechecker helpers -/

namespace EnvRel

variable {envF envS : TypeEnv} (h : EnvRel envF envS)
include h

theorem inv_bool (b : BoolType) : Inv envF (.bool b) := by
  simp [Inv, CedarType.entityTypesAll]

theorem S_of_inv_entity {e : EntityType} (hi : Inv envF (.entity e)) : S envF e = true := by
  simpa [Inv, CedarType.entityTypesAll] using hi

theorem S_of_inv_set_entity {e : EntityType} (hi : Inv envF (.set (.entity e))) : S envF e = true := by
  simpa [Inv, CedarType.entityTypesAll] using hi

theorem typeOfLit_agree (p : Prim) (hp : ∀ u, p = .entityUID u → GoodLit envF u) :
    typeOfLit p envS = typeOfLit p envF ∧
    ∀ t c', typeOfLit p envF = .ok (t, c') → AllTy (Inv envF) t := by
  cases p with
  | entityUID u =>
    have hu := hp u rfl
    constructor
    · simp only [typeOfLit, h.ets, h.contains_agree_good hu]
    · intro t c' ht
      simp only [typeOfLit] at ht
      split at ht
      · simp only [Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        exact .lit (by simpa [Inv, CedarType.entityTypesAll] using h.good_S hu)
      · cases ht
  | bool b =>
    cases b <;> refine ⟨rfl, ?_⟩ <;> intro t c' ht <;>
      simp only [typeOfLit, Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at ht <;>
      obtain ⟨rfl, _⟩ := ht <;> exact .lit (h.inv_bool _)
  | int i | string s =>
    refine ⟨rfl, ?_⟩
    intro t c' ht
    simp only [typeOfLit, Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, _⟩ := ht
    exact .lit (by simp [Inv, CedarType.entityTypesAll])

theorem typeOfVar_agree (v : Var) :
    typeOfVar v envS = typeOfVar v envF ∧
    ∀ t c', typeOfVar v envF = .ok (t, c') → AllTy (Inv envF) t := by
  constructor
  · simp only [typeOfVar, h.reqty]
  intro t c' ht
  cases v <;> simp only [typeOfVar, Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at ht <;>
    obtain ⟨rfl, _⟩ := ht <;> apply AllTy.var
  · simpa [Inv, CedarType.entityTypesAll] using ets_imp_S h.prin
  · simp [Inv, CedarType.entityTypesAll, S]
  · simpa [Inv, CedarType.entityTypesAll] using ets_imp_S h.res
  · exact inv_of_ets h.ctx

omit h in
theorem actionUID?_some {x : Expr} {acts : ActionSchema} {u : EntityUID}
    (hx : actionUID? x acts = some u) : entityUID? x = some u ∧ acts.contains u = true := by
  unfold actionUID? at hx
  cases he : entityUID? x with
  | none => simp [he] at hx
  | some u' =>
    simp [he, bind] at hx
    obtain ⟨hc, rfl⟩ := hx
    exact ⟨rfl, hc⟩

theorem actionUID?_agree {x : Expr} (hx : ∀ u, entityUID? x = some u → GoodLit envF u) :
    actionUID? x envS.acts = actionUID? x envF.acts := by
  unfold actionUID?
  cases he : entityUID? x with
  | none => simp
  | some u' => simp [h.contains_agree_good (hx u' he)]

/-- An action UID found by `actionUID?` on a good literal is the request action. -/
theorem actionUID?_is_action {x : Expr} {u : EntityUID}
    (hx : ∀ u, entityUID? x = some u → GoodLit envF u) (hu : actionUID? x envF.acts = some u) :
    u = envF.reqty.action := by
  obtain ⟨he, hc⟩ := actionUID?_some hu
  rcases hx u he with hv | hv
  · exact absurd (isValid_imp_contains hv) (h.disj u hc)
  · exact hv

theorem typeOfInₑ_agree {ety₁ ety₂ : EntityType} {x₁ x₂ : Expr}
    (hx₁ : ∀ u, entityUID? x₁ = some u → GoodLit envF u)
    (h₁ : S envF ety₁ = true) (h₂ : S envF ety₂ = true) :
    typeOfInₑ ety₁ ety₂ x₁ x₂ envS = typeOfInₑ ety₁ ety₂ x₁ x₂ envF := by
  simp only [typeOfInₑ, h.actionUID?_agree hx₁]
  split
  · rename_i uid₁ uid₂ hu₁ _
    rw [h.actionUID?_is_action hx₁ hu₁, h.desc]
  · rw [h.descendentOf_agree h₁ h₂]

theorem typeOfInₛ_agree {ety₁ ety₂ : EntityType} {x₁ x₂ : Expr}
    (hx₁ : ∀ u, entityUID? x₁ = some u → GoodLit envF u)
    (h₁ : S envF ety₁ = true) (h₂ : S envF ety₂ = true) :
    typeOfInₛ ety₁ ety₂ x₁ x₂ envS = typeOfInₛ ety₁ ety₂ x₁ x₂ envF := by
  simp only [typeOfInₛ, h.actionUID?_agree hx₁]
  split
  · rename_i uid₁ uids hu₁ _
    rw [h.actionUID?_is_action hx₁ hu₁]
    simp only [h.desc]
  · rw [h.descendentOf_agree h₁ h₂]

theorem tags?_none_not_contains {ety : EntityType} (ht : envF.ets.tags? ety = none) :
    envF.ets.contains ety = false := by
  simp only [EntitySchema.tags?, Option.map_eq_none_iff] at ht
  simp [EntitySchema.contains, ht]

theorem attrs?_none_not_contains {ety : EntityType} (ht : envF.ets.attrs? ety = none) :
    envF.ets.contains ety = false := by
  simp only [EntitySchema.attrs?, Option.map_eq_none_iff] at ht
  simp [EntitySchema.contains, ht]

theorem typeOfHasTag_agree {ety : EntityType} {x t : Expr} {c : Capabilities}
    (hS : S envF ety = true) :
    typeOfHasTag ety x t c envS = typeOfHasTag ety x t c envF := by
  simp only [typeOfHasTag, h.ets]
  split
  · rfl
  · rfl
  · rename_i hn
    rw [h.actionType?_agree hS (h.tags?_none_not_contains hn)]

theorem typeOfHasAttr_agree {ty : TypedExpr} {x : Expr} {a : Attr} {c : Capabilities}
    (hi : Inv envF ty.typeOf) :
    typeOfHasAttr ty x a c envS = typeOfHasAttr ty x a c envF ∧
    ∀ t c', typeOfHasAttr ty x a c envF = .ok (t, c') → AllTy (Inv envF) ty →
      AllTy (Inv envF) t := by
  constructor
  · simp only [typeOfHasAttr, h.ets]
    split
    · rfl
    · rename_i ety hty
      split
      · rfl
      · rename_i hn
        rw [hty] at hi
        rw [h.actionType?_agree (h.S_of_inv_entity hi) (h.attrs?_none_not_contains hn)]
    · rfl
  · intro t c' ht hall
    simp only [typeOfHasAttr] at ht
    split at ht
    · rename_i rty _
      cases hr : hasAttrInRecord rty x a c true with
      | error => simp [hr, bind, Except.bind] at ht
      | ok r =>
        simp only [hr, bind, Except.bind, ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        refine .hasAttr hall ?_
        simp only [hasAttrInRecord] at hr
        split at hr <;> (try split at hr) <;>
          simp only [ok, Except.ok.injEq] at hr <;> subst hr <;> exact h.inv_bool _
    · split at ht
      · rename_i rty _
        cases hr : hasAttrInRecord rty x a c false with
        | error => simp [hr, bind, Except.bind] at ht
        | ok r =>
          simp only [hr, bind, Except.bind, ok, Except.ok.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, _⟩ := ht
          refine .hasAttr hall ?_
          simp only [hasAttrInRecord] at hr
          split at hr <;> (try split at hr) <;>
            simp only [ok, Except.ok.injEq] at hr <;> subst hr <;> exact h.inv_bool _
      · split at ht
        · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, _⟩ := ht
          exact .hasAttr hall (h.inv_bool _)
        · cases ht
    · cases ht

theorem getAttrInRecord_inv {ty : CedarType} {rty : RecordType} {x : Expr} {a : Attr}
    {c : Capabilities} {aty : CedarType} {c' : Capabilities}
    (hi : Inv envF (.record rty)) (hg : getAttrInRecord ty rty x a c = .ok (aty, c')) :
    Inv envF aty := by
  simp only [getAttrInRecord] at hg
  split at hg
  · rename_i aty' hf
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, _⟩ := hg
    have := entityTypesAll_record_mem hi (Map.find?_mem_toList hf)
    simpa [Inv, Qualified.getType] using this
  · rename_i aty' hf
    split at hg
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, _⟩ := hg
      have := entityTypesAll_record_mem hi (Map.find?_mem_toList hf)
      simpa [Inv, Qualified.getType] using this
    · cases hg
  · cases hg

theorem typeOfGetAttr_agree {ty : TypedExpr} {x : Expr} {a : Attr} {c : Capabilities}
    (hi : Inv envF ty.typeOf) :
    typeOfGetAttr ty x a c envS = typeOfGetAttr ty x a c envF ∧
    ∀ t c', typeOfGetAttr ty x a c envF = .ok (t, c') → AllTy (Inv envF) ty →
      AllTy (Inv envF) t := by
  constructor
  · simp only [typeOfGetAttr, h.ets]
  · intro t c' ht hall
    simp only [typeOfGetAttr] at ht
    split at ht
    · rename_i rty hty
      cases hr : getAttrInRecord ty.typeOf rty x a c with
      | error => simp [hr, bind, Except.bind] at ht
      | ok r =>
        simp only [hr, bind, Except.bind, ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        rw [hty] at hi
        exact .getAttr hall (h.getAttrInRecord_inv hi hr)
    · rename_i ety hty
      split at ht
      · rename_i rty hrty
        cases hr : getAttrInRecord ty.typeOf rty x a c with
        | error => simp [hr, bind, Except.bind] at ht
        | ok r =>
          simp only [hr, bind, Except.bind, ok, Except.ok.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, _⟩ := ht
          exact .getAttr hall (h.getAttrInRecord_inv (inv_of_ets (h.attrs ety rty hrty)) hr)
      · cases ht
    · cases ht

theorem typeOfEq_inv {ty₁ ty₂ : TypedExpr} {x₁ x₂ : Expr} {t : TypedExpr} {c' : Capabilities}
    (ht : typeOfEq ty₁ ty₂ x₁ x₂ = .ok (t, c')) (h₁ : AllTy (Inv envF) ty₁)
    (h₂ : AllTy (Inv envF) ty₂) : AllTy (Inv envF) t := by
  simp only [typeOfEq] at ht
  split at ht
  · split at ht <;>
    simp only [Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at ht <;>
    obtain ⟨rfl, _⟩ := ht <;> exact .binaryApp h₁ h₂ (h.inv_bool _)
  · split at ht
    · simp only [Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, _⟩ := ht; exact .binaryApp h₁ h₂ (h.inv_bool _)
    · split at ht
      · simp only [Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht; exact .binaryApp h₁ h₂ (h.inv_bool _)
      · cases ht

theorem typeOfHasTag_bool {ety : EntityType} {x tg : Expr} {c : Capabilities} {ty : CedarType}
    {c' : Capabilities} (ht : typeOfHasTag ety x tg c envF = .ok (ty, c')) : ∃ b, ty = .bool b := by
  simp only [typeOfHasTag] at ht
  split at ht
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht; exact ⟨_, ht.1.symm⟩
  · split at ht <;> simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht <;> exact ⟨_, ht.1.symm⟩
  · split at ht
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht; exact ⟨_, ht.1.symm⟩
    · cases ht

theorem typeOfGetTag_inv {ety : EntityType} {x tg : Expr} {c : Capabilities} {ty : CedarType}
    {c' : Capabilities} (ht : typeOfGetTag ety x tg c envF = .ok (ty, c')) : Inv envF ty := by
  simp only [typeOfGetTag] at ht
  split at ht
  · cases ht
  · rename_i tty htags
    split at ht
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, _⟩ := ht
      exact inv_of_ets (h.tags ety tty htags)
    · cases ht
  · cases ht

omit h in
theorem ifLubThenBool_bool {ty₁ ty₂ ty : CedarType} {c' : Capabilities}
    (ht : ifLubThenBool ty₁ ty₂ = .ok (ty, c')) : ty = .bool .anyBool := by
  simp only [ifLubThenBool] at ht
  split at ht
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht; exact ht.1.symm
  · cases ht

theorem typeOfBinaryApp_agree {op : BinaryOp} {ty₁ ty₂ : TypedExpr} {x₁ x₂ : Expr} {c : Capabilities}
    (hi₁ : Inv envF ty₁.typeOf) (hi₂ : Inv envF ty₂.typeOf)
    (hx₁ : ∀ u, entityUID? x₁ = some u → GoodLit envF u) :
    typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c envS = typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c envF ∧
    ∀ t c', typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c envF = .ok (t, c') →
      AllTy (Inv envF) ty₁ → AllTy (Inv envF) ty₂ → AllTy (Inv envF) t := by
  constructor
  · unfold typeOfBinaryApp
    split
    case h_2 ety₁ ety₂ e₁ e₂ =>
      rw [e₁] at hi₁; rw [e₂] at hi₂
      rw [h.typeOfInₑ_agree hx₁ (h.S_of_inv_entity hi₁) (h.S_of_inv_entity hi₂)]
    case h_3 ety₁ ety₂ e₁ e₂ =>
      rw [e₁] at hi₁; rw [e₂] at hi₂
      rw [h.typeOfInₛ_agree hx₁ (h.S_of_inv_entity hi₁) (h.S_of_inv_set_entity hi₂)]
    case h_4 ety₁ e₁ _ =>
      rw [e₁] at hi₁
      rw [h.typeOfHasTag_agree (h.S_of_inv_entity hi₁)]
    case h_5 =>
      simp only [typeOfGetTag, h.ets]
    all_goals rfl
  · intro t c' ht h₁ h₂
    unfold typeOfBinaryApp at ht
    split at ht
    case h_1 => exact h.typeOfEq_inv ht h₁ h₂
    case h_4 =>
      simp only [bind, Except.bind] at ht
      split at ht
      · cases ht
      · rename_i r hr
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        obtain ⟨b, hb⟩ := h.typeOfHasTag_bool hr
        exact .binaryApp h₁ h₂ (hb ▸ h.inv_bool b)
    case h_5 =>
      simp only [bind, Except.bind] at ht
      split at ht
      · cases ht
      · rename_i r hr
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        exact .binaryApp h₁ h₂ (h.typeOfGetTag_inv hr)
    case h_15 | h_16 | h_17 =>
      simp only [bind, Except.bind] at ht
      split at ht
      · cases ht
      · rename_i r hr
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        exact .binaryApp h₁ h₂ (ifLubThenBool_bool hr ▸ h.inv_bool _)
    case h_18 => cases ht
    all_goals
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, _⟩ := ht
      exact .binaryApp h₁ h₂ (by simp [Inv, CedarType.entityTypesAll])

theorem typeOfExtHasAttr_agree : ∀ (attrs : List Attr) (ty₁ : TypedExpr) (x₁ : Expr)
    (c : Capabilities), Inv envF ty₁.typeOf → AllTy (Inv envF) ty₁ →
    typeOfExtHasAttr ty₁ x₁ attrs c envS = typeOfExtHasAttr ty₁ x₁ attrs c envF
  | [], _, _, _, _, _ => by simp [typeOfExtHasAttr]
  | [a], ty₁, x₁, c, hi, _ => by
    simp only [typeOfExtHasAttr, (h.typeOfHasAttr_agree (x := x₁) (a := a) (c := c) hi).1]
  | a :: b :: rest, ty₁, x₁, c, hi, hall => by
    simp only [typeOfExtHasAttr, (h.typeOfHasAttr_agree (x := x₁) (a := a) (c := c) hi).1]
    cases hh : typeOfHasAttr ty₁ x₁ a c envF with
    | error => rfl
    | ok p =>
      obtain ⟨tyHas, ci⟩ := p
      simp only [bind, Except.bind]
      split
      · rfl
      · rw [(h.typeOfGetAttr_agree (x := x₁) (a := a) (c := c ∪ ci) hi).1]
        cases hg : typeOfGetAttr ty₁ x₁ a (c ∪ ci) envF with
        | error => rfl
        | ok q =>
          obtain ⟨tyNext, cn⟩ := q
          simp only
          have hallN := (h.typeOfGetAttr_agree (x := x₁) (a := a) (c := c ∪ ci) hi).2 _ _ hg hall
          rw [typeOfExtHasAttr_agree (b :: rest) tyNext (.getAttr x₁ a) (c ∪ ci) hallN.top hallN]

omit h in
theorem typeOfConstructor_ty {α} {mk : String → Option α} {xs : List Expr} {ty ty' : CedarType}
    {c' : Capabilities} (ht : typeOfConstructor mk xs ty = .ok (ty', c')) : ty' = ty := by
  simp only [typeOfConstructor] at ht
  split at ht
  · split at ht
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht; exact ht.1.symm
    · cases ht
  · cases ht

theorem typeOfCall_inv {xfn : ExtFun} {tys : List TypedExpr} {xs : List Expr} {t : TypedExpr}
    {c' : Capabilities} (ht : typeOfCall xfn tys xs = .ok (t, c'))
    (hall : ∀ x ∈ tys, AllTy (Inv envF) x) : AllTy (Inv envF) t := by
  unfold typeOfCall at ht
  split at ht
  case h_1 | h_2 | h_3 | h_4 =>
    simp only [bind, Except.bind] at ht
    split at ht
    · cases ht
    · rename_i r hr
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, _⟩ := ht
      rw [typeOfConstructor_ty hr]
      exact .call hall (by simp [Inv, CedarType.entityTypesAll])
  case h_13 =>
    simp only [typeOfIsInRange] at ht
    split at ht
    · split at ht
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        exact .call hall (by simp [Inv, CedarType.entityTypesAll])
      · cases ht
    · cases ht
  all_goals first
    | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
       obtain ⟨rfl, _⟩ := ht
       exact .call hall (by simp [Inv, CedarType.entityTypesAll]))
    | cases ht

theorem typeOfIf_inv {ty₁ : TypedExpr} {c₁ : Capabilities} {r₂ r₃ : ResultType}
    {t : TypedExpr} {c' : Capabilities} (ht : typeOfIf (ty₁, c₁) r₂ r₃ = .ok (t, c'))
    (h₁ : AllTy (Inv envF) ty₁)
    (h₂ : ∀ t c, r₂ = .ok (t, c) → AllTy (Inv envF) t)
    (h₃ : ∀ t c, r₃ = .ok (t, c) → AllTy (Inv envF) t) : AllTy (Inv envF) t := by
  simp only [typeOfIf] at ht
  split at ht
  · cases hr : r₂ with
    | error => simp [hr, bind, Except.bind] at ht
    | ok p =>
      simp only [hr, bind, Except.bind, ok, Except.ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, _⟩ := ht
      have := h₂ _ _ hr
      exact .ite h₁ this this this.top
  · cases hr : r₃ with
    | error => simp [hr, bind, Except.bind] at ht
    | ok p =>
      simp only [hr, bind, Except.bind, ok, Except.ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, _⟩ := ht
      have := h₃ _ _ hr
      exact .ite h₁ this this this.top
  · cases hr₂ : r₂ with
    | error => simp [hr₂, bind, Except.bind] at ht
    | ok p₂ =>
      cases hr₃ : r₃ with
      | error => simp [hr₂, hr₃, bind, Except.bind] at ht
      | ok p₃ =>
        simp only [hr₂, hr₃, bind, Except.bind] at ht
        split at ht
        · rename_i ty hlub
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, _⟩ := ht
          have a₂ := h₂ _ _ hr₂
          have a₃ := h₃ _ _ hr₃
          exact .ite h₁ a₂ a₃ (lub_inv hlub a₂.top)
        · cases ht
  · cases ht

theorem typeOfAnd_inv {ty₁ : TypedExpr} {c₁ : Capabilities} {r₂ : ResultType}
    {t : TypedExpr} {c' : Capabilities} (ht : typeOfAnd (ty₁, c₁) r₂ = .ok (t, c'))
    (h₁ : AllTy (Inv envF) ty₁)
    (h₂ : ∀ t c, r₂ = .ok (t, c) → AllTy (Inv envF) t) : AllTy (Inv envF) t := by
  simp only [typeOfAnd] at ht
  split at ht
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, _⟩ := ht; exact h₁
  · cases hr : r₂ with
    | error => simp [hr, bind, Except.bind] at ht
    | ok p =>
      simp only [hr, bind, Except.bind] at ht
      have a₂ := h₂ _ _ hr
      split at ht
      all_goals first
        | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
           obtain ⟨rfl, _⟩ := ht; exact .and h₁ a₂ (h.inv_bool _))
        | cases ht
  · cases ht

theorem typeOfOr_inv {ty₁ : TypedExpr} {c₁ : Capabilities} {r₂ : ResultType}
    {t : TypedExpr} {c' : Capabilities} (ht : typeOfOr (ty₁, c₁) r₂ = .ok (t, c'))
    (h₁ : AllTy (Inv envF) ty₁)
    (h₂ : ∀ t c, r₂ = .ok (t, c) → AllTy (Inv envF) t) : AllTy (Inv envF) t := by
  simp only [typeOfOr] at ht
  split at ht
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, _⟩ := ht; exact h₁
  · cases hr : r₂ with
    | error => simp [hr, bind, Except.bind] at ht
    | ok p =>
      simp only [hr, bind, Except.bind] at ht
      have a₂ := h₂ _ _ hr
      split at ht
      · rename_i b hb
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        exact .or h₁ a₂ (hb ▸ h.inv_bool b)
      · cases ht
  · cases hr : r₂ with
    | error => simp [hr, bind, Except.bind] at ht
    | ok p =>
      simp only [hr, bind, Except.bind] at ht
      have a₂ := h₂ _ _ hr
      split at ht
      all_goals first
        | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
           obtain ⟨rfl, _⟩ := ht; exact .or h₁ a₂ (h.inv_bool _))
        | cases ht
  · cases ht

theorem typeOfUnaryApp_inv {op : UnaryOp} {ty₁ : TypedExpr} {t : TypedExpr} {c' : Capabilities}
    (ht : typeOfUnaryApp op ty₁ = .ok (t, c')) (h₁ : AllTy (Inv envF) ty₁) :
    AllTy (Inv envF) t := by
  simp only [typeOfUnaryApp] at ht
  split at ht
  all_goals first
    | (simp only [Function.comp, ok, Except.ok.injEq, Prod.mk.injEq] at ht
       obtain ⟨rfl, _⟩ := ht; exact .unaryApp h₁ (by simp [Inv, CedarType.entityTypesAll]))
    | cases ht

omit h in
theorem entityUID?_mem {x : Expr} {u : EntityUID} (he : entityUID? x = some u) :
    u ∈ x.literalUIDs := by
  unfold entityUID? at he
  split at he
  · cases he; simp [Expr.literalUIDs, Set.mem_singleton]
  · cases he

omit h in
theorem justType_ok {r : ResultType} {t : TypedExpr} (hr : justType r = .ok t) :
    ∃ c, r = .ok (t, c) := by
  cases r with
  | error => simp [justType, Except.map] at hr
  | ok p =>
    obtain ⟨t', c⟩ := p
    simp [justType, Except.map] at hr
    exact ⟨c, by rw [hr]⟩

/-- Main typechecker transfer: for an expression whose entity literals are
    declared entities or the request action, typechecking in the sliced
    environment gives exactly the full-environment result, and every node of
    the typed result mentions only declared entity types or the action type. -/
theorem typeOf_agree (x : Expr) (hx : ∀ u ∈ x.literalUIDs, GoodLit envF u) (c : Capabilities) :
    typeOf x c envS = typeOf x c envF ∧
    ∀ t c', typeOf x c envF = .ok (t, c') → AllTy (Inv envF) t := by
  match x with
  | .lit p =>
    have := h.typeOfLit_agree p (fun u hu => hx u (by
      subst hu; simp [Expr.literalUIDs, Set.mem_singleton]))
    simpa only [typeOf] using this
  | .var v => simpa only [typeOf] using h.typeOfVar_agree v
  | .ite x₁ x₂ x₃ =>
    simp only [Expr.literalUIDs] at hx
    obtain ⟨hx₁₂, hx₃⟩ := forall_mem_union' hx
    obtain ⟨hx₁, hx₂⟩ := forall_mem_union' hx₁₂
    have ih₁ := fun c => typeOf_agree x₁ hx₁ c
    have ih₂ := fun c => typeOf_agree x₂ hx₂ c
    have ih₃ := fun c => typeOf_agree x₃ hx₃ c
    have e₁ : ∀ c, typeOf x₁ c envS = typeOf x₁ c envF := fun c => (ih₁ c).1
    have e₂ : ∀ c, typeOf x₂ c envS = typeOf x₂ c envF := fun c => (ih₂ c).1
    have e₃ : ∀ c, typeOf x₃ c envS = typeOf x₃ c envF := fun c => (ih₃ c).1
    constructor
    · simp only [typeOf, e₁, e₂, e₃]
    · intro t c' ht
      simp only [typeOf] at ht
      cases h₁ : typeOf x₁ c envF with
      | error => simp [h₁, bind, Except.bind] at ht
      | ok p =>
        obtain ⟨ty₁, c₁⟩ := p
        simp only [h₁, bind, Except.bind] at ht
        exact h.typeOfIf_inv ht ((ih₁ c).2 _ _ h₁) ((ih₂ _).2) ((ih₃ _).2)
  | .and x₁ x₂ =>
    simp only [Expr.literalUIDs] at hx
    obtain ⟨hx₁, hx₂⟩ := forall_mem_union' hx
    have ih₁ := fun c => typeOf_agree x₁ hx₁ c
    have ih₂ := fun c => typeOf_agree x₂ hx₂ c
    have e₁ : ∀ c, typeOf x₁ c envS = typeOf x₁ c envF := fun c => (ih₁ c).1
    have e₂ : ∀ c, typeOf x₂ c envS = typeOf x₂ c envF := fun c => (ih₂ c).1
    constructor
    · simp only [typeOf, e₁, e₂]
    · intro t c' ht
      simp only [typeOf] at ht
      cases h₁ : typeOf x₁ c envF with
      | error => simp [h₁, bind, Except.bind] at ht
      | ok p =>
        obtain ⟨ty₁, c₁⟩ := p
        simp only [h₁, bind, Except.bind] at ht
        exact h.typeOfAnd_inv ht ((ih₁ c).2 _ _ h₁) ((ih₂ _).2)
  | .or x₁ x₂ =>
    simp only [Expr.literalUIDs] at hx
    obtain ⟨hx₁, hx₂⟩ := forall_mem_union' hx
    have ih₁ := fun c => typeOf_agree x₁ hx₁ c
    have ih₂ := fun c => typeOf_agree x₂ hx₂ c
    have e₁ : ∀ c, typeOf x₁ c envS = typeOf x₁ c envF := fun c => (ih₁ c).1
    have e₂ : ∀ c, typeOf x₂ c envS = typeOf x₂ c envF := fun c => (ih₂ c).1
    constructor
    · simp only [typeOf, e₁, e₂]
    · intro t c' ht
      simp only [typeOf] at ht
      cases h₁ : typeOf x₁ c envF with
      | error => simp [h₁, bind, Except.bind] at ht
      | ok p =>
        obtain ⟨ty₁, c₁⟩ := p
        simp only [h₁, bind, Except.bind] at ht
        exact h.typeOfOr_inv ht ((ih₁ c).2 _ _ h₁) ((ih₂ _).2)
  | .unaryApp op x₁ =>
    simp only [Expr.literalUIDs] at hx
    have ih₁ := typeOf_agree x₁ hx c
    constructor
    · simp only [typeOf, ih₁.1]
    · intro t c' ht
      simp only [typeOf] at ht
      cases h₁ : typeOf x₁ c envF with
      | error => simp [h₁, bind, Except.bind] at ht
      | ok p =>
        obtain ⟨ty₁, c₁⟩ := p
        simp only [h₁, bind, Except.bind] at ht
        exact h.typeOfUnaryApp_inv ht (ih₁.2 _ _ h₁)
  | .binaryApp op x₁ x₂ =>
    simp only [Expr.literalUIDs] at hx
    obtain ⟨hx₁, hx₂⟩ := forall_mem_union' hx
    have ih₁ := typeOf_agree x₁ hx₁ c
    have ih₂ := typeOf_agree x₂ hx₂ c
    have hu₁ : ∀ u, entityUID? x₁ = some u → GoodLit envF u :=
      fun u hu => hx₁ u (entityUID?_mem hu)
    have key : ∀ ty₁ c₁ ty₂ c₂, typeOf x₁ c envF = .ok (ty₁, c₁) →
        typeOf x₂ c envF = .ok (ty₂, c₂) →
        typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c envS = typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c envF ∧
        ∀ t c', typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c envF = .ok (t, c') → AllTy (Inv envF) t := by
      intro ty₁ c₁ ty₂ c₂ h₁ h₂
      have a₁ := ih₁.2 _ _ h₁
      have a₂ := ih₂.2 _ _ h₂
      have := h.typeOfBinaryApp_agree (op := op) (x₂ := x₂) (c := c) a₁.top a₂.top hu₁
      exact ⟨this.1, fun t c' ht => this.2 t c' ht a₁ a₂⟩
    constructor
    · simp only [typeOf, ih₁.1, ih₂.1]
      cases h₁ : typeOf x₁ c envF with
      | error => rfl
      | ok p₁ =>
        cases h₂ : typeOf x₂ c envF with
        | error => rfl
        | ok p₂ =>
          simp only [bind, Except.bind]
          exact (key _ _ _ _ h₁ h₂).1
    · intro t c' ht
      simp only [typeOf] at ht
      cases h₁ : typeOf x₁ c envF with
      | error => simp [h₁, bind, Except.bind] at ht
      | ok p₁ =>
        cases h₂ : typeOf x₂ c envF with
        | error => simp [h₁, h₂, bind, Except.bind] at ht
        | ok p₂ =>
          simp only [h₁, h₂, bind, Except.bind] at ht
          exact (key _ _ _ _ h₁ h₂).2 _ _ ht
  | .hasAttr x₁ a =>
    simp only [Expr.literalUIDs] at hx
    have ih₁ := typeOf_agree x₁ hx c
    constructor
    · simp only [typeOf, ih₁.1]
      cases h₁ : typeOf x₁ c envF with
      | error => rfl
      | ok p₁ =>
        simp only [bind, Except.bind]
        exact (h.typeOfHasAttr_agree (ih₁.2 _ _ h₁).top).1
    · intro t c' ht
      simp only [typeOf] at ht
      cases h₁ : typeOf x₁ c envF with
      | error => simp [h₁, bind, Except.bind] at ht
      | ok p₁ =>
        simp only [h₁, bind, Except.bind] at ht
        have a₁ := ih₁.2 _ _ h₁
        exact (h.typeOfHasAttr_agree a₁.top).2 _ _ ht a₁
  | .getAttr x₁ a =>
    simp only [Expr.literalUIDs] at hx
    have ih₁ := typeOf_agree x₁ hx c
    constructor
    · simp only [typeOf, ih₁.1]
      cases h₁ : typeOf x₁ c envF with
      | error => rfl
      | ok p₁ =>
        simp only [bind, Except.bind]
        exact (h.typeOfGetAttr_agree (ih₁.2 _ _ h₁).top).1
    · intro t c' ht
      simp only [typeOf] at ht
      cases h₁ : typeOf x₁ c envF with
      | error => simp [h₁, bind, Except.bind] at ht
      | ok p₁ =>
        simp only [h₁, bind, Except.bind] at ht
        have a₁ := ih₁.2 _ _ h₁
        exact (h.typeOfGetAttr_agree a₁.top).2 _ _ ht a₁
  | .extHasAttr x₁ a attrs =>
    simp only [Expr.literalUIDs] at hx
    have ih₁ := typeOf_agree x₁ hx c
    constructor
    · simp only [typeOf, ih₁.1]
      cases h₁ : typeOf x₁ c envF with
      | error => rfl
      | ok p₁ =>
        simp only [bind, Except.bind]
        have a₁ := ih₁.2 _ _ h₁
        rw [h.typeOfExtHasAttr_agree (a :: attrs) p₁.1 x₁ c a₁.top a₁]
    · intro t c' ht
      simp only [typeOf] at ht
      cases h₁ : typeOf x₁ c envF with
      | error => simp [h₁, bind, Except.bind] at ht
      | ok p₁ =>
        simp only [h₁, bind, Except.bind] at ht
        have a₁ := ih₁.2 _ _ h₁
        split at ht
        · cases ht
        · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, _⟩ := ht
          exact .extHasAttr a₁ (h.inv_bool _)
  | .set xs =>
    simp only [Expr.literalUIDs, List.mapUnion₁_eq_mapUnion Expr.literalUIDs] at hx
    have ih : ∀ y ∈ xs, typeOf y c envS = typeOf y c envF ∧
        ∀ t c', typeOf y c envF = .ok (t, c') → AllTy (Inv envF) t :=
      fun y hy => typeOf_agree y (forall_mem_mapUnion hx y hy) c
    have hm : xs.mapM (fun y => justType (typeOf y c envS)) =
        xs.mapM (fun y => justType (typeOf y c envF)) :=
      List.mapM_congr (fun y hy => by rw [(ih y hy).1])
    constructor
    · simp only [typeOf, List.mapM₁_eq_mapM (fun y => justType (typeOf y c envS)),
        List.mapM₁_eq_mapM (fun y => justType (typeOf y c envF)), hm]
    · intro t c' ht
      simp only [typeOf, List.mapM₁_eq_mapM (fun y => justType (typeOf y c envF))] at ht
      cases hts : xs.mapM (fun y => justType (typeOf y c envF)) with
      | error => simp [hts, bind, Except.bind] at ht
      | ok tys =>
        simp only [hts, bind, Except.bind] at ht
        have hall : ∀ ty ∈ tys, AllTy (Inv envF) ty := by
          intro ty hty
          obtain ⟨y, hy, hjy⟩ := List.mapM_ok_implies_all_from_ok hts ty hty
          obtain ⟨cy, hcy⟩ := justType_ok hjy
          exact (ih y hy).2 _ _ hcy
        simp only [typeOfSet] at ht
        split at ht
        · cases ht
        · rename_i hd tl
          split at ht
          · rename_i ty hfold
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
            obtain ⟨rfl, _⟩ := ht
            refine .set hall ?_
            have := foldlM_lub_inv (ok := S envF) _ _ _ hfold
              (hall hd (List.mem_cons_self ..)).top
            simpa [Inv, CedarType.entityTypesAll] using this
          · cases ht
  | .record axs =>
    simp only [Expr.literalUIDs,
      List.mapUnion₂_eq_mapUnion (fun x : Attr × Expr => x.snd.literalUIDs)] at hx
    have ih : ∀ ax ∈ axs, typeOf ax.2 c envS = typeOf ax.2 c envF ∧
        ∀ t c', typeOf ax.2 c envF = .ok (t, c') → AllTy (Inv envF) t := by
      intro ⟨k, y⟩ hy
      have : sizeOf y < sizeOf (Expr.record axs) := by
        have h₁ := List.sizeOf_lt_of_mem hy
        simp only [Prod.mk.sizeOf_spec, Expr.record.sizeOf_spec] at h₁ ⊢
        omega
      exact typeOf_agree y
        (forall_mem_mapUnion (f := fun x : Attr × Expr => x.snd.literalUIDs) hx (k, y) hy) c
    let f := fun (env : TypeEnv) (x : Attr × Expr) =>
      Except.map (fun x₁ : (TypedExpr × Capabilities) => (x.fst, x₁.fst)) (typeOf x.snd c env)
    have hm2 : ∀ env, (axs.mapM₂ fun x => Except.map (fun x_1 : TypedExpr × Capabilities =>
        (x.1.fst, x_1.fst)) (typeOf x.1.snd c env)) = axs.mapM (f env) :=
      fun env => List.mapM₂_eq_mapM (f env) axs
    have hm : axs.mapM (f envS) = axs.mapM (f envF) :=
      List.mapM_congr (fun ax hax => by simp only [f, (ih ax hax).1])
    constructor
    · simp only [typeOf, hm2, hm]
    · intro t c' ht
      simp only [typeOf, hm2] at ht
      cases hts : axs.mapM (f envF) with
      | error => simp [hts, bind, Except.bind] at ht
      | ok atys =>
        simp only [hts, bind, Except.bind, ok, Except.ok.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, _⟩ := ht
        have hall : ∀ aty ∈ atys, AllTy (Inv envF) aty.2 := by
          intro aty haty
          obtain ⟨ax, hax, hfx⟩ := List.mapM_ok_implies_all_from_ok hts aty haty
          simp only [f] at hfx
          cases hty : typeOf ax.2 c envF with
          | error => simp [hty, Except.map] at hfx
          | ok p =>
            simp only [hty, Except.map, Except.ok.injEq] at hfx
            subst hfx
            exact (ih ax hax).2 _ _ hty
        refine .record hall ?_
        simp only [Inv]
        rw [entityTypesAll_record_iff]
        intro kq hkq
        have hkq' := Map.mem_make_mem_list hkq
        obtain ⟨aty, haty, heq⟩ := List.mem_map.mp hkq'
        subst heq
        simpa [Inv, Qualified.getType] using (hall aty haty).top
  | .call xfn xs =>
    simp only [Expr.literalUIDs, List.mapUnion₁_eq_mapUnion Expr.literalUIDs] at hx
    have ih : ∀ y ∈ xs, typeOf y c envS = typeOf y c envF ∧
        ∀ t c', typeOf y c envF = .ok (t, c') → AllTy (Inv envF) t :=
      fun y hy => typeOf_agree y (forall_mem_mapUnion hx y hy) c
    have hm : xs.mapM (fun y => justType (typeOf y c envS)) =
        xs.mapM (fun y => justType (typeOf y c envF)) :=
      List.mapM_congr (fun y hy => by rw [(ih y hy).1])
    constructor
    · simp only [typeOf, List.mapM₁_eq_mapM (fun y => justType (typeOf y c envS)),
        List.mapM₁_eq_mapM (fun y => justType (typeOf y c envF)), hm]
    · intro t c' ht
      simp only [typeOf, List.mapM₁_eq_mapM (fun y => justType (typeOf y c envF))] at ht
      cases hts : xs.mapM (fun y => justType (typeOf y c envF)) with
      | error => simp [hts, bind, Except.bind] at ht
      | ok tys =>
        simp only [hts, bind, Except.bind] at ht
        have hall : ∀ ty ∈ tys, AllTy (Inv envF) ty := by
          intro ty hty
          obtain ⟨y, hy, hjy⟩ := List.mapM_ok_implies_all_from_ok hts ty hty
          obtain ⟨cy, hcy⟩ := justType_ok hjy
          exact (ih y hy).2 _ _ hcy
        exact h.typeOfCall_inv ht hall
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hy; omega)
    | (simp only [Expr.record.sizeOf_spec] at this; omega)

end EnvRel

/-! ## 5e. Residual invariant and `evaluate` agreement -/

/-- The only type shapes the TPE evaluator inspects in an env-sensitive way. -/
def QB (envF : TypeEnv) : CedarType → Bool
  | .entity e => EnvRel.S envF e
  | .set (.entity e) => EnvRel.S envF e
  | _ => true

inductive RAllTy (P : CedarType → Prop) : Residual → Prop where
  | val {v ty} : P ty → RAllTy P (.val v ty)
  | var {v ty} : P ty → RAllTy P (.var v ty)
  | ite {a b c ty} : RAllTy P a → RAllTy P b → RAllTy P c → P ty → RAllTy P (.ite a b c ty)
  | and {a b ty} : RAllTy P a → RAllTy P b → P ty → RAllTy P (.and a b ty)
  | or {a b ty} : RAllTy P a → RAllTy P b → P ty → RAllTy P (.or a b ty)
  | unaryApp {op a ty} : RAllTy P a → P ty → RAllTy P (.unaryApp op a ty)
  | binaryApp {op a b ty} : RAllTy P a → RAllTy P b → P ty → RAllTy P (.binaryApp op a b ty)
  | getAttr {a attr ty} : RAllTy P a → P ty → RAllTy P (.getAttr a attr ty)
  | hasAttr {a attr ty} : RAllTy P a → P ty → RAllTy P (.hasAttr a attr ty)
  | extHasAttr {a attr attrs ty} : RAllTy P a → P ty → RAllTy P (.extHasAttr a attr attrs ty)
  | set {xs ty} : (∀ x ∈ xs, RAllTy P x) → P ty → RAllTy P (.set xs ty)
  | record {axs ty} : (∀ ax ∈ axs, RAllTy P ax.2) → P ty → RAllTy P (.record axs ty)
  | call {xfn xs ty} : (∀ x ∈ xs, RAllTy P x) → P ty → RAllTy P (.call xfn xs ty)
  | error {ty} : P ty → RAllTy P (.error ty)

theorem QB_of_inv {envF : TypeEnv} {ty : CedarType} (h : EnvRel.Inv envF ty) : QB envF ty = true := by
  unfold QB
  split
  · simpa [EnvRel.Inv, CedarType.entityTypesAll] using h
  · simpa [EnvRel.Inv, CedarType.entityTypesAll] using h
  · rfl

theorem QB_liftBoolTypes {envF : TypeEnv} {ty : CedarType} (h : QB envF ty = true) :
    QB envF ty.liftBoolTypes = true := by
  cases ty with
  | set s =>
    cases s <;> simp_all [QB, CedarType.liftBoolTypes]
  | _ => simp_all [QB, CedarType.liftBoolTypes]

theorem RAllTy_of_AllTy {envF : TypeEnv} {t : TypedExpr} (h : AllTy (EnvRel.Inv envF) t) :
    RAllTy (fun ty => QB envF ty = true) t.liftBoolTypes.toResidual := by
  induction h with
  | lit hp =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .val (QB_liftBoolTypes (QB_of_inv hp))
  | var hp =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .var (QB_liftBoolTypes (QB_of_inv hp))
  | ite _ _ _ hp ih₁ ih₂ ih₃ =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .ite ih₁ ih₂ ih₃ (QB_liftBoolTypes (QB_of_inv hp))
  | and _ _ hp ih₁ ih₂ =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .and ih₁ ih₂ (QB_liftBoolTypes (QB_of_inv hp))
  | or _ _ hp ih₁ ih₂ =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .or ih₁ ih₂ (QB_liftBoolTypes (QB_of_inv hp))
  | unaryApp _ hp ih =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .unaryApp ih (QB_liftBoolTypes (QB_of_inv hp))
  | binaryApp _ _ hp ih₁ ih₂ =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .binaryApp ih₁ ih₂ (QB_liftBoolTypes (QB_of_inv hp))
  | getAttr _ hp ih =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .getAttr ih (QB_liftBoolTypes (QB_of_inv hp))
  | hasAttr _ hp ih =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .hasAttr ih (QB_liftBoolTypes (QB_of_inv hp))
  | extHasAttr _ hp ih =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual]
    exact .extHasAttr ih (QB_liftBoolTypes (QB_of_inv hp))
  | @set xs ty _ hp ih =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual,
      List.map₁_eq_map TypedExpr.liftBoolTypes, List.map₁_eq_map TypedExpr.toResidual]
    refine .set ?_ (QB_liftBoolTypes (QB_of_inv hp))
    intro r hr
    simp only [List.map_map, List.mem_map, Function.comp] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact ih x hx
  | @record axs ty _ hp ih =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual,
      List.map₂_eq_map (fun (p : Attr × TypedExpr) => (p.1, p.2.liftBoolTypes)),
      List.map₂_eq_map (fun (p : Attr × TypedExpr) => (p.1, p.2.toResidual))]
    refine .record ?_ (QB_liftBoolTypes (QB_of_inv hp))
    intro r hr
    simp only [List.map_map, List.mem_map, Function.comp] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact ih x hx
  | @call xfn xs ty _ hp ih =>
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual,
      List.map₁_eq_map TypedExpr.liftBoolTypes, List.map₁_eq_map TypedExpr.toResidual]
    refine .call ?_ (QB_liftBoolTypes (QB_of_inv hp))
    intro r hr
    simp only [List.map_map, List.mem_map, Function.comp] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact ih x hx

namespace EnvRel

variable {envF envS : TypeEnv} (h : EnvRel envF envS)
include h

theorem tryDecideResidual₂_agree {op : BinaryOp} {r₁ r₂ : Residual}
    (q₁ : QB envF r₁.typeOf = true) (q₂ : QB envF r₂.typeOf = true) :
    tryDecideResidual₂ envS op r₁ r₂ = tryDecideResidual₂ envF op r₁ r₂ := by
  unfold tryDecideResidual₂
  split
  · split
    case h_1 ety₁ ety₂ e₁ e₂ =>
      rw [e₁] at q₁; rw [e₂] at q₂
      simp only [QB] at q₁ q₂
      rw [h.descendentOf_agree q₁ q₂]
    case h_2 ety₁ ety₂ e₁ e₂ =>
      rw [e₁] at q₁; rw [e₂] at q₂
      simp only [QB] at q₁ q₂
      rw [h.descendentOf_agree q₁ q₂]
    case h_4 => rw [h.ets]
    all_goals rfl
  · rfl

theorem apply₂_agree {op : BinaryOp} {r₁ r₂ : Residual} {es : PartialEntities} {ty : CedarType}
    (q₁ : QB envF r₁.typeOf = true) (q₂ : QB envF r₂.typeOf = true) :
    apply₂ envS op r₁ r₂ es ty = apply₂ envF op r₁ r₂ es ty := by
  unfold Cedar.TPE.apply₂
  rw [h.tryDecideResidual₂_agree q₁ q₂]

theorem tryDecideHasResidual_agree (r : Residual) (a : Attr) :
    tryDecideHasResidual envS r a = tryDecideHasResidual envF r a := by
  simp only [tryDecideHasResidual, h.ets]

theorem hasAttr_agree (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) :
    Cedar.TPE.hasAttr envS r a es ty = Cedar.TPE.hasAttr envF r a es ty := by
  simp only [Cedar.TPE.hasAttr, h.tryDecideHasResidual_agree]

theorem extHasAttr_tryDecide_agree (r : Residual) (a : Attr) (attrs : List Attr) (ty : CedarType) :
    extHasAttr.tryDecide envS r a attrs ty = extHasAttr.tryDecide envF r a attrs ty := by
  simp only [extHasAttr.tryDecide, h.tryDecideHasResidual_agree]

theorem extHasAttr_loop_agree (es : PartialEntities) (ty : CedarType) :
    ∀ (attrs : List Attr) (m : Map Attr Value),
    extHasAttr.loop envS m attrs es ty = extHasAttr.loop envF m attrs es ty
  | [], _ => by simp [extHasAttr.loop]
  | [_], _ => by simp [extHasAttr.loop]
  | a :: b :: rest, m => by
    simp only [extHasAttr.loop]
    split
    · rfl
    · split
      · exact extHasAttr_loop_agree es ty (b :: rest) _
      · split
        · exact h.extHasAttr_tryDecide_agree _ _ _ _
        · rfl

theorem extHasAttr_agree (r : Residual) (a : Attr) (attrs : List Attr) (es : PartialEntities)
    (ty : CedarType) :
    Cedar.TPE.extHasAttr envS r a attrs es ty = Cedar.TPE.extHasAttr envF r a attrs es ty := by
  simp only [Cedar.TPE.extHasAttr, h.extHasAttr_loop_agree, h.extHasAttr_tryDecide_agree]

end EnvRel

section Tops

variable {envF : TypeEnv}

theorem QB_bool (b : BoolType) : QB envF (.bool b) = true := rfl

theorem varₚ_top (req : PartialRequest) (v : Var) (ty : CedarType) :
    (varₚ req v ty).typeOf = ty := by
  cases v <;> simp only [varₚ, varₚ.varₒ]
  all_goals
    unfold someOrSelf
    split <;> rfl

theorem ite_top {c t e : Residual} {ty : CedarType} (qt : QB envF t.typeOf = true)
    (qe : QB envF e.typeOf = true) (q : QB envF ty = true) :
    QB envF (Cedar.TPE.ite c t e ty).typeOf = true := by
  unfold Cedar.TPE.ite
  split
  · split <;> assumption
  · exact q
  · exact q

theorem and_top {l r : Residual} {ty : CedarType} (ql : QB envF l.typeOf = true)
    (qr : QB envF r.typeOf = true) (q : QB envF ty = true) :
    QB envF (Cedar.TPE.and l r ty).typeOf = true := by
  unfold Cedar.TPE.and
  split
  all_goals first
    | assumption
    | rfl
    | (split <;> first | rfl | assumption)

theorem or_top {l r : Residual} {ty : CedarType} (ql : QB envF l.typeOf = true)
    (qr : QB envF r.typeOf = true) (q : QB envF ty = true) :
    QB envF (Cedar.TPE.or l r ty).typeOf = true := by
  unfold Cedar.TPE.or
  split
  all_goals first
    | assumption
    | rfl
    | (split <;> first | rfl | assumption)

theorem someOrError_top (o : Option Value) (ty : CedarType) : (someOrError o ty).typeOf = ty := by
  cases o <;> rfl

theorem apply₁_top (op : UnaryOp) (r : Residual) (ty : CedarType) :
    (Cedar.TPE.apply₁ op r ty).typeOf = ty := by
  unfold Cedar.TPE.apply₁
  split
  · rfl
  · split
    · rfl
    · split
      · exact someOrError_top _ _
      · rfl

theorem apply₂_top (env : TypeEnv) (op : BinaryOp) (r₁ r₂ : Residual) (es : PartialEntities)
    (ty : CedarType) : (Cedar.TPE.apply₂ env op r₁ r₂ es ty).typeOf = ty := by
  unfold Cedar.TPE.apply₂
  split
  · rfl
  · rfl
  · split
    · rfl
    · split
      · split
        all_goals first
          | rfl
          | exact someOrError_top _ _
          | (simp only [someOrSelf]; split <;> rfl)
          | (simp only [Cedar.TPE.getTag]; split
             · exact someOrError_top _ _
             · rfl)
      · rfl

theorem getAttr_top (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) :
    (Cedar.TPE.getAttr r a es ty).typeOf = ty := by
  unfold Cedar.TPE.getAttr
  split
  · rfl
  · split
    · exact someOrError_top _ _
    · rfl

theorem hasAttr_top (env : TypeEnv) (r : Residual) (a : Attr) (es : PartialEntities)
    {ty : CedarType} (q : QB envF ty = true) :
    QB envF (Cedar.TPE.hasAttr env r a es ty).typeOf = true := by
  unfold Cedar.TPE.hasAttr
  split
  · exact q
  · split
    · exact q
    · split
      · rfl
      · exact q

theorem extHasAttr_tryDecide_top (env : TypeEnv) (r : Residual) (a : Attr) (attrs : List Attr)
    {ty : CedarType} (q : QB envF ty = true) :
    QB envF (extHasAttr.tryDecide env r a attrs ty).typeOf = true := by
  unfold extHasAttr.tryDecide
  split <;> exact q

theorem extHasAttr_loop_top (env : TypeEnv) (es : PartialEntities) {ty : CedarType}
    (q : QB envF ty = true) :
    ∀ (attrs : List Attr) (m : Map Attr Value),
    QB envF (extHasAttr.loop env m attrs es ty).typeOf = true
  | [], _ => by simp [extHasAttr.loop]; rfl
  | [_], _ => by simp [extHasAttr.loop]; rfl
  | a :: b :: rest, m => by
    simp only [extHasAttr.loop]
    split
    · rfl
    · split
      · exact extHasAttr_loop_top env es q (b :: rest) _
      · split
        · exact extHasAttr_tryDecide_top env _ _ _ q
        · exact q

theorem extHasAttr_top (env : TypeEnv) (r : Residual) (a : Attr) (attrs : List Attr)
    (es : PartialEntities) {ty : CedarType} (q : QB envF ty = true) :
    QB envF (Cedar.TPE.extHasAttr env r a attrs es ty).typeOf = true := by
  unfold Cedar.TPE.extHasAttr
  split
  · exact q
  · split
    · exact extHasAttr_loop_top env es q _ _
    · exact extHasAttr_tryDecide_top env _ _ _ q

theorem set_top (rs : List Residual) (ty : CedarType) : (Cedar.TPE.set rs ty).typeOf = ty := by
  unfold Cedar.TPE.set; split
  · rfl
  · split <;> rfl

theorem record_top (rs : List (Attr × Residual)) (ty : CedarType) :
    (Cedar.TPE.record rs ty).typeOf = ty := by
  unfold Cedar.TPE.record; split
  · rfl
  · split <;> rfl

theorem call_top (xfn : ExtFun) (rs : List Residual) (ty : CedarType) :
    (Cedar.TPE.call xfn rs ty).typeOf = ty := by
  unfold Cedar.TPE.call; split
  · exact someOrError_top _ _
  · split <;> rfl

end Tops

namespace EnvRel

variable {envF envS : TypeEnv} (h : EnvRel envF envS)
include h

theorem find_action : ∃ e, envF.acts.find? envF.reqty.action = some e ∧
    envS.acts.find? envF.reqty.action = some e := by
  have hS := h.actS
  simp only [ActionSchema.contains, Option.isSome_iff_exists] at hS
  obtain ⟨e, he⟩ := hS
  exact ⟨e, h.sub _ _ he, he⟩

/-- `descendentOf` from the action type to the type of one of the action's
    ancestors agrees. -/
theorem descendentOf_agree_anc {u : EntityUID}
    (hd : envF.acts.descendentOf envF.reqty.action u = true) :
    envS.descendentOf envF.reqty.action.ty u.ty = envF.descendentOf envF.reqty.action.ty u.ty := by
  obtain ⟨e, hF, hS⟩ := h.find_action
  simp only [TypeEnv.descendentOf, h.ets]
  split
  · rfl
  · rename_i hne
    have hnone : envF.ets.find? envF.reqty.action.ty = none := by
      have := h.act_ty_not_ets
      simp only [EntitySchema.contains, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at this
      exact this
    simp only [hnone]
    have hau : u ∈ e.ancestors := by
      simp only [ActionSchema.descendentOf, hF] at hd
      split at hd
      · rename_i heq; rw [beq_iff_eq] at heq; subst heq; exact absurd rfl hne
      · exact (Set.contains_prop_bool_equiv).mp hd
    have hany : ∀ (acts : ActionSchema), acts.find? envF.reqty.action = some e →
        acts.maybeDescendentOf envF.reqty.action.ty u.ty = true := by
      intro acts hf
      simp only [ActionSchema.maybeDescendentOf, List.any_eq_true]
      refine ⟨(envF.reqty.action, e), Map.find?_mem_toList hf, ?_⟩
      simp only [decide_true, Bool.true_and, Set.any, List.any_eq_true, beq_iff_eq]
      exact ⟨u, (Set.mem_elts_iff_mem_set _ _).mpr hau, rfl⟩
    rw [hany _ hS, hany _ hF]

theorem tryDecideResidual₂_agree_of {op : BinaryOp} {r₁ r₂ : Residual}
    (hd : ∀ e₁ e₂, r₁.typeOf = .entity e₁ →
      (r₂.typeOf = .entity e₂ ∨ r₂.typeOf = .set (.entity e₂)) →
      envS.descendentOf e₁ e₂ = envF.descendentOf e₁ e₂) :
    tryDecideResidual₂ envS op r₁ r₂ = tryDecideResidual₂ envF op r₁ r₂ := by
  unfold tryDecideResidual₂
  split
  · split
    case h_1 ety₁ ety₂ e₁ e₂ => rw [hd ety₁ ety₂ e₁ (.inl e₂)]
    case h_2 ety₁ ety₂ e₁ e₂ => rw [hd ety₁ ety₂ e₁ (.inr e₂)]
    case h_4 => rw [h.ets]
    all_goals rfl
  · rfl

end EnvRel

/-- TPE evaluation agrees on the full and sliced environments for residuals
    whose entity-typed nodes mention only declared entity types or the action
    type. -/
theorem EnvRel.evaluate_agree {envF envS : TypeEnv} (h : EnvRel envF envS)
    (req : PartialRequest) (es : PartialEntities) {x : Residual}
    (hx : RAllTy (fun ty => QB envF ty = true) x) :
    Cedar.TPE.evaluate envS x req es = Cedar.TPE.evaluate envF x req es ∧
    QB envF (Cedar.TPE.evaluate envF x req es).typeOf = true := by
  induction hx with
  | val hp => simp only [Cedar.TPE.evaluate]; exact ⟨trivial, hp⟩
  | var hp => simp only [Cedar.TPE.evaluate, varₚ_top]; exact ⟨trivial, hp⟩
  | error hp => simp only [Cedar.TPE.evaluate]; exact ⟨trivial, hp⟩
  | ite _ _ _ hp ih₁ ih₂ ih₃ =>
    simp only [Cedar.TPE.evaluate, ih₁.1, ih₂.1, ih₃.1]
    exact ⟨trivial, ite_top ih₂.2 ih₃.2 hp⟩
  | and _ _ hp ih₁ ih₂ =>
    simp only [Cedar.TPE.evaluate, ih₁.1, ih₂.1]
    exact ⟨trivial, and_top ih₁.2 ih₂.2 hp⟩
  | or _ _ hp ih₁ ih₂ =>
    simp only [Cedar.TPE.evaluate, ih₁.1, ih₂.1]
    exact ⟨trivial, or_top ih₁.2 ih₂.2 hp⟩
  | unaryApp _ hp ih =>
    simp only [Cedar.TPE.evaluate, ih.1, apply₁_top]
    exact ⟨trivial, hp⟩
  | binaryApp _ _ hp ih₁ ih₂ =>
    simp only [Cedar.TPE.evaluate, ih₁.1, ih₂.1, apply₂_top]
    exact ⟨h.apply₂_agree ih₁.2 ih₂.2, hp⟩
  | getAttr _ hp ih =>
    simp only [Cedar.TPE.evaluate, ih.1, getAttr_top]
    exact ⟨trivial, hp⟩
  | hasAttr _ hp ih =>
    simp only [Cedar.TPE.evaluate, ih.1]
    exact ⟨h.hasAttr_agree _ _ _ _, hasAttr_top _ _ _ _ hp⟩
  | extHasAttr _ hp ih =>
    simp only [Cedar.TPE.evaluate, ih.1]
    exact ⟨h.extHasAttr_agree _ _ _ _ _, extHasAttr_top _ _ _ _ _ hp⟩
  | @set xs ty _ hp ih =>
    simp only [Cedar.TPE.evaluate, set_top]
    refine ⟨?_, hp⟩
    rw [List.map₁_eq_map (fun x => Cedar.TPE.evaluate envS x req es),
      List.map₁_eq_map (fun x => Cedar.TPE.evaluate envF x req es)]
    congr 1
    exact List.map_congr_left (fun x hx => (ih x hx).1)
  | @record axs ty _ hp ih =>
    simp only [Cedar.TPE.evaluate, record_top]
    refine ⟨?_, hp⟩
    rw [List.map₁_eq_map (fun (p : Attr × Residual) => (p.1, Cedar.TPE.evaluate envS p.2 req es)),
      List.map₁_eq_map (fun (p : Attr × Residual) => (p.1, Cedar.TPE.evaluate envF p.2 req es))]
    congr 1
    exact List.map_congr_left (fun x hx => by rw [(ih x hx).1])
  | @call xfn xs ty _ hp ih =>
    simp only [Cedar.TPE.evaluate, call_top]
    refine ⟨?_, hp⟩
    rw [List.map₁_eq_map (fun x => Cedar.TPE.evaluate envS x req es),
      List.map₁_eq_map (fun x => Cedar.TPE.evaluate envF x req es)]
    congr 1
    exact List.map_congr_left (fun x hx => (ih x hx).1)

/-! ## Literals after `substituteAction` -/

theorem mapOnVars_literalUIDs {P : EntityUID → Prop} {f : Var → Expr}
    (hf : ∀ v, ∀ u ∈ (f v).literalUIDs, P u) :
    ∀ (x : Expr), (∀ u ∈ x.literalUIDs, P u) → ∀ u ∈ (mapOnVars f x).literalUIDs, P u
  | .lit _, hx => by simpa [mapOnVars] using hx
  | .var v, _ => by simpa [mapOnVars] using hf v
  | .ite x₁ x₂ x₃, hx => by
    simp only [Expr.literalUIDs] at hx
    obtain ⟨hx₁₂, hx₃⟩ := forall_mem_union' hx
    obtain ⟨hx₁, hx₂⟩ := forall_mem_union' hx₁₂
    have i₁ := mapOnVars_literalUIDs hf x₁ hx₁
    have i₂ := mapOnVars_literalUIDs hf x₂ hx₂
    have i₃ := mapOnVars_literalUIDs hf x₃ hx₃
    intro u hu
    simp only [mapOnVars, Expr.literalUIDs, Set.mem_union] at hu
    rcases hu with (hu | hu) | hu
    · exact i₁ u hu
    · exact i₂ u hu
    · exact i₃ u hu
  | .and x₁ x₂, hx | .or x₁ x₂, hx | .binaryApp _ x₁ x₂, hx => by
    simp only [Expr.literalUIDs] at hx
    obtain ⟨hx₁, hx₂⟩ := forall_mem_union' hx
    have i₁ := mapOnVars_literalUIDs hf x₁ hx₁
    have i₂ := mapOnVars_literalUIDs hf x₂ hx₂
    intro u hu
    simp only [mapOnVars, Expr.literalUIDs, Set.mem_union] at hu
    rcases hu with hu | hu
    · exact i₁ u hu
    · exact i₂ u hu
  | .unaryApp _ x₁, hx | .getAttr x₁ _, hx | .hasAttr x₁ _, hx | .extHasAttr x₁ _ _, hx => by
    simp only [Expr.literalUIDs] at hx
    have i₁ := mapOnVars_literalUIDs hf x₁ hx
    intro u hu
    simp only [mapOnVars, Expr.literalUIDs] at hu
    exact i₁ u hu
  | .set xs, hx | .call _ xs, hx => by
    simp only [Expr.literalUIDs, List.mapUnion₁_eq_mapUnion Expr.literalUIDs] at hx
    intro u hu
    simp only [mapOnVars, Expr.literalUIDs, List.mapUnion₁_eq_mapUnion Expr.literalUIDs,
      List.map₁_eq_map (mapOnVars f)] at hu
    obtain ⟨y, hy, huy⟩ := (List.mem_mapUnion_iff_mem_exists u).mp hu
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact mapOnVars_literalUIDs hf z (forall_mem_mapUnion hx z hz) u huy
  | .record axs, hx => by
    simp only [Expr.literalUIDs,
      List.mapUnion₂_eq_mapUnion (fun x : Attr × Expr => x.snd.literalUIDs)] at hx
    intro u hu
    simp only [mapOnVars, Expr.literalUIDs,
      List.mapUnion₂_eq_mapUnion (fun x : Attr × Expr => x.snd.literalUIDs),
      List.map₂_eq_map (fun (p : Attr × Expr) => (p.1, mapOnVars f p.2))] at hu
    obtain ⟨y, hy, huy⟩ := (List.mem_mapUnion_iff_mem_exists u).mp hu
    obtain ⟨⟨k, z⟩, hz, rfl⟩ := List.mem_map.mp hy
    have : sizeOf z < sizeOf (Expr.record axs) := by
      have h₁ := List.sizeOf_lt_of_mem hz
      simp only [Prod.mk.sizeOf_spec, Expr.record.sizeOf_spec] at h₁ ⊢
      omega
    exact mapOnVars_literalUIDs hf z
      (forall_mem_mapUnion (f := fun x : Attr × Expr => x.snd.literalUIDs) hx (k, z) hz) u huy
termination_by x => sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hz; omega)
    | (simp only [Expr.record.sizeOf_spec] at this; omega)

theorem substituteAction_literalUIDs {P : EntityUID → Prop} {a : EntityUID} (ha : P a)
    {x : Expr} (hx : ∀ u ∈ x.literalUIDs, P u) :
    ∀ u ∈ (substituteAction a x).literalUIDs, P u := by
  apply mapOnVars_literalUIDs _ x hx
  intro v u hu
  cases v <;> simp [Expr.literalUIDs, Set.mem_singleton, Set.not_mem_empty] at hu
  subst hu; exact ha

/-! ## 5f. Compositional agreement for policy pieces -/

/-- An expression whose successful full-environment typing is reproduced in the
    sliced environment, with the same TPE evaluation. -/
def PieceAgree (envF envS : TypeEnv) (x : Expr) : Prop :=
  ∀ c t c', typeOf x c envF = .ok (t, c') →
    typeOf x c envS = .ok (t, c') ∧
    ∀ req es, Cedar.TPE.evaluate envS t.liftBoolTypes.toResidual req es =
      Cedar.TPE.evaluate envF t.liftBoolTypes.toResidual req es

namespace EnvRel

variable {envF envS : TypeEnv} (h : EnvRel envF envS)
include h

theorem piece_of_good {x : Expr} (hx : ∀ u ∈ x.literalUIDs, GoodLit envF u) :
    PieceAgree envF envS x := by
  intro c t c' ht
  have hag := h.typeOf_agree x hx c
  refine ⟨hag.1 ▸ ht, fun req es => ?_⟩
  exact (h.evaluate_agree req es (RAllTy_of_AllTy (hag.2 _ _ ht))).1

omit h in
theorem piece_and {x y : Expr} (hx : PieceAgree envF envS x) (hy : PieceAgree envF envS y) :
    PieceAgree envF envS (.and x y) := by
  intro c t c' ht
  obtain ⟨t₁, c₁, h₁, hcase⟩ := SlicedPoliciesDropped.typeOf_and_ok ht
  obtain ⟨hS₁, he₁⟩ := hx c t₁ c₁ h₁
  rcases hcase with ⟨hff, rfl⟩ | ⟨b, t₂, c₂, bt, hb, hbne, h₂, rfl, _, _⟩
  · refine ⟨?_, he₁⟩
    rw [SlicedPoliciesActionInAny.typeOf_and', hS₁]
    rw [SlicedPoliciesActionInAny.typeOf_and', h₁] at ht
    simp only [bind, Except.bind] at ht ⊢
    rw [← ht]
    simp only [typeOfAnd, hff]
  · obtain ⟨hS₂, he₂⟩ := hy _ t₂ c₂ h₂
    refine ⟨?_, ?_⟩
    · rw [SlicedPoliciesActionInAny.typeOf_and', hS₁]
      rw [SlicedPoliciesActionInAny.typeOf_and', h₁] at ht
      simp only [bind, Except.bind] at ht ⊢
      rw [hS₂, ← ht, h₂]
    · intro req es
      simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual, Cedar.TPE.evaluate]
      rw [he₁, he₂]

/-- `action in A` for an ancestor (or self) `A` of the request action. -/
theorem piece_mem_lit {uid : EntityUID}
    (hd : envF.acts.descendentOf envF.reqty.action uid = true) :
    PieceAgree envF envS (.binaryApp .mem (.lit (.entityUID envF.reqty.action))
      (.lit (.entityUID uid))) := by
  intro c t c' ht
  have hcA : envS.acts.contains envF.reqty.action = envF.acts.contains envF.reqty.action := by
    rw [h.actS, h.actF]
  have hcU := h.closureContains uid hd
  have hdS : envS.acts.descendentOf envF.reqty.action uid = true := by rw [h.desc]; exact hd
  have key : ∀ env : TypeEnv, env.acts.contains envF.reqty.action = true →
      (env.ets.isValidEntityUID uid || env.acts.contains uid) = true →
      env.acts.descendentOf envF.reqty.action uid = true →
      typeOf (.binaryApp .mem (.lit (.entityUID envF.reqty.action)) (.lit (.entityUID uid))) c env =
      .ok (.binaryApp .mem (.lit (.entityUID envF.reqty.action) (.entity envF.reqty.action.ty))
        (.lit (.entityUID uid) (.entity uid.ty)) (.bool .tt), ∅) := by
    intro env hc hv hd'
    simp [typeOf, typeOfLit, hc, hv, typeOfBinaryApp, TypedExpr.typeOf, typeOfInₑ, actionUID?,
      entityUID?, hd', ok]
  by_cases hv : (envF.ets.isValidEntityUID uid || envF.acts.contains uid) = true
  · have hvS : (envS.ets.isValidEntityUID uid || envS.acts.contains uid) = true := by
      rw [h.ets, hcU]; exact hv
    rw [key envF h.actF hv hd] at ht
    simp only [Except.ok.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    refine ⟨key envS h.actS hvS hdS, fun req es => ?_⟩
    simp only [TypedExpr.liftBoolTypes, TypedExpr.toResidual, Cedar.TPE.evaluate]
    unfold Cedar.TPE.apply₂
    rw [h.tryDecideResidual₂_agree_of]
    intro e₁ e₂ he₁ he₂
    simp only [Residual.typeOf, CedarType.liftBoolTypes, CedarType.entity.injEq] at he₁ he₂
    rcases he₂ with he₂ | he₂
    · subst he₁ he₂; exact h.descendentOf_agree_anc hd
    · cases he₂
  · simp [typeOf, typeOfLit, h.actF, hv, err, ok, bind, Except.bind] at ht

open SlicedPoliciesActionInAny in
/-- `action in [A₁, ..., Aₙ]` where every `Aᵢ` is the request action or one of
    its ancestors (the shape kept by `sliceForAction`). -/
theorem piece_mem_set {us : List EntityUID}
    (hd : ∀ u ∈ us, envF.acts.descendentOf envF.reqty.action u = true) :
    PieceAgree envF envS (actExpr envF.reqty.action us) := by
  intro c t c' ht
  obtain ⟨e, hne, hv, rfl, rfl⟩ := typeOf_actExpr h.actF ht
  have hvS : ∀ u ∈ us, validUID envS u = true ∧ u.ty = e := by
    intro u hu
    refine ⟨?_, (hv u hu).2⟩
    have := (hv u hu).1
    simp only [validUID, h.ets, h.closureContains u (hd u hu)] at this ⊢
    exact this
  have hany : us.any (envS.acts.descendentOf envF.reqty.action ·) =
      us.any (envF.acts.descendentOf envF.reqty.action ·) := by
    simp only [h.desc]
  refine ⟨?_, fun req es => ?_⟩
  · rw [typeOf_actExpr_of h.actS hne hvS, hany]
  · have hev : ∀ env : TypeEnv, ∀ b : BoolType,
        Cedar.TPE.evaluate env (actTyped envF.reqty.action us e b).liftBoolTypes.toResidual req es =
        Cedar.TPE.apply₂ env .mem (.val (.prim (.entityUID envF.reqty.action)) (.entity envF.reqty.action.ty))
          (.val (.set (Set.make (us.map fun x => Value.prim (Prim.entityUID x)))) (.set (.entity e)))
          es (.bool b.lift) := by
      intro env b
      simp [actTyped, TypedExpr.liftBoolTypes, TypedExpr.toResidual, CedarType.liftBoolTypes,
        Cedar.TPE.evaluate, List.map₁_eq_map, typedLits, List.map_map, Function.comp_def,
        Cedar.TPE.set]
      rw [List.map₁_eq_map (fun x => Cedar.TPE.evaluate env x req es)]
      simp only [List.map_map, Function.comp_def, Cedar.TPE.evaluate]
      rw [mapM_asValue_vals]
    rw [hev, hev]
    unfold Cedar.TPE.apply₂
    rw [h.tryDecideResidual₂_agree_of]
    intro e₁ e₂ he₁ he₂
    simp only [Residual.typeOf, CedarType.entity.injEq] at he₁ he₂
    rcases he₂ with he₂ | he₂
    · cases he₂
    · simp only [CedarType.set.injEq, CedarType.entity.injEq] at he₂
      subst he₁ he₂
      obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil us hne
      rw [← (hv u hu).2]
      exact h.descendentOf_agree_anc (hd u hu)

theorem goodLit_of_ets {full : Schema} (hets : envF.ets = full.ets) (hacts : envF.acts = full.acts)
    {u : EntityUID} (hok : LitOk full u = true) (hty : envF.ets.contains u.ty = true) :
    GoodLit envF u := by
  left
  simp only [LitOk, Bool.or_eq_true] at hok
  rcases hok with hok | hok
  · rw [hets]; exact hok
  · exact absurd hty (h.disj u (hacts ▸ hok))

theorem goodLit_of_nonaction {full : Schema} (hets : envF.ets = full.ets)
    {u : EntityUID} (hok : LitOk full u = true) (hna : full.acts.actionType? u.ty = false) :
    GoodLit envF u := by
  left
  simp only [LitOk, Bool.or_eq_true] at hok
  rcases hok with hok | hok
  · rw [hets]; exact hok
  · rw [actionType?_of_contains hok] at hna; cases hna

/-- Every principal/resource scope of a kept policy agrees. -/
theorem piece_var_scope {full : Schema} (hets : envF.ets = full.ets) (hacts : envF.acts = full.acts)
    (hwfenv : TypeEnv.WellFormed envF) {sc : Scope} {v : Var} {ety : EntityType}
    (hety : envF.ets.contains ety = true) (hm : Scope.mayMatchType sc ety envF = true)
    (hcheck : checkEntities full (sc.toExpr v) = .ok ()) :
    PieceAgree envF envS (substituteAction envF.reqty.action (sc.toExpr v)) := by
  apply h.piece_of_good
  refine substituteAction_literalUIDs (.inr rfl) ?_
  intro u hu
  exact h.goodLit_of_ets hets hacts (checkEntities_lits _ hcheck u hu)
    ((scope_types_ets hwfenv hety hm).1 u hu)

/-- The action scope of a kept policy agrees. -/
theorem piece_action_scope {asc as' : ActionScope}
    (has : ActionScope.sliceForAction asc envF.reqty.action envF.acts = some as') :
    PieceAgree envF envS (substituteAction envF.reqty.action as'.toExpr) := by
  rcases sliceForAction_cases has with rfl | ⟨uids, rfl, rfl⟩
  · cases as' with
    | actionScope sc =>
      simp only [ActionScope.toExpr]
      rw [SlicedPoliciesDropped.subst_scope_action]
      cases sc with
      | any => exact h.piece_of_good (by intro u hu; simp [Expr.literalUIDs, Set.not_mem_empty] at hu)
      | eq uid =>
        simp only [ActionScope.sliceForAction] at has
        split at has
        · rename_i heq
          rw [beq_iff_eq] at heq
          subst heq
          apply h.piece_of_good
          intro u hu
          simp [Expr.literalUIDs, Set.mem_union, Set.mem_singleton] at hu
          subst hu; exact .inr rfl
        · cases has
      | mem uid =>
        simp only [ActionScope.sliceForAction] at has
        split at has
        · exact h.piece_mem_lit (by assumption)
        · cases has
      | is ety =>
        apply h.piece_of_good
        intro u hu
        simp [Expr.literalUIDs, Set.mem_singleton] at hu
        subst hu; exact .inr rfl
      | isMem ety uid =>
        simp only [ActionScope.sliceForAction] at has
        split at has
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          apply piece_and
          · apply h.piece_of_good
            intro u hu
            simp [Expr.literalUIDs, Set.mem_singleton] at hu
            subst hu; exact .inr rfl
          · exact h.piece_mem_lit hc.2
        · cases has
    | actionInAny uids =>
      rw [SlicedPoliciesActionInAny.subst_actionInAny]
      simp only [ActionScope.sliceForAction] at has
      split at has
      · cases has
      · simp only [Option.some.injEq, ActionScope.actionInAny.injEq] at has
        apply h.piece_mem_set
        intro u hu
        rw [← has] at hu
        exact (List.mem_filter.mp hu).2
  · rw [SlicedPoliciesActionInAny.subst_actionInAny]
    exact h.piece_mem_set (fun u hu => (List.mem_filter.mp hu).2)

/-- The whole substituted policy expression of a kept policy agrees. -/
theorem piece_policy {full : Schema} {policies : Policies} {p p' : Policy}
    (hets : envF.ets = full.ets) (hacts : envF.acts = full.acts)
    (hwfenv : TypeEnv.WellFormed envF)
    (hmem : p ∈ policies)
    (hnolits : full.noActionLiteralsInConditions policies = true)
    (hsl : Policy.sliceForRequestEnv p envF = some p')
    (hcheck : checkEntities full p'.toExpr = .ok ()) :
    PieceAgree envF envS (substituteAction envF.reqty.action p'.toExpr) := by
  obtain ⟨hpm, hrm, as', has, rfl⟩ := sliceForRequestEnv_facts hsl
  rw [SlicedPoliciesActionInAny.policy_toExpr_check] at hcheck
  obtain ⟨hcP, _, hcR, hcC⟩ := hcheck
  rw [SlicedPoliciesActionInAny.policy_toExpr_subst]
  refine piece_and ?_ (piece_and ?_ (piece_and ?_ ?_))
  · have hpe : p.principalScope.toExpr = p.principalScope.scope.toExpr .principal := by
      cases p.principalScope; rfl
    simp only at hcP ⊢
    rw [hpe] at hcP ⊢
    exact h.piece_var_scope hets hacts hwfenv h.prin hpm hcP
  · exact h.piece_action_scope has
  · have hre : p.resourceScope.toExpr = p.resourceScope.scope.toExpr .resource := by
      cases p.resourceScope; rfl
    simp only at hcR ⊢
    rw [hre] at hcR ⊢
    exact h.piece_var_scope hets hacts hwfenv h.res hrm hcR
  · apply h.piece_of_good
    refine substituteAction_literalUIDs (.inr rfl) ?_
    intro u hu
    simp only at hu hcC
    have hok := checkEntities_lits _ hcC u hu
    obtain ⟨c, hc, hu'⟩ := mem_conditions_literalUIDs hu
    simp only [Schema.noActionLiteralsInConditions, List.all_eq_true, Bool.not_eq_true'] at hnolits
    have hna := hnolits p hmem u ((Set.mem_elts_iff_mem_set _ _).mpr
      (List.mem_mem_implies_mem_mapUnion (f := fun c : Condition => c.body.literalUIDs) hu' hc))
    exact h.goodLit_of_nonaction hets hok hna

end EnvRel

/-! ## 6. Building `EnvRel` from the top-level hypotheses -/

theorem envRel_of_slice {sliced full : Schema} {req : PartialRequest} {envF envS : TypeEnv}
    (hslice : sliced.IsActionSliceOf full req.action)
    (hwfF : full.validateWellFormed = .ok ())
    (hwfS : sliced.validateWellFormed = .ok ())
    (hno : full.noActionTypedAttrs = true)
    (hF : validatePartialRequest full req = .ok envF)
    (hS : validatePartialRequest sliced req = .ok envS) :
    EnvRel envF envS := by
  have henv := validatePartialRequest_slice_env hslice rfl hF hS
  have hwfenvF := wf_of_environment hwfF (validatePartialRequest_environment hF).1
  have hwfenvS := wf_of_environment hwfS (validatePartialRequest_environment hS).1
  obtain ⟨ase, hfind, hets, hacts, hact⟩ := SlicedPoliciesActionInAny.env_facts hF
  obtain ⟨ase', hfind', hp, hr, henvF⟩ := environment?_facts (validatePartialRequest_environment hF).1
  rw [hfind] at hfind'; cases hfind'
  obtain ⟨hpc, hrc⟩ := env_principal_resource_ets hno hF
  have hnoA := hno
  simp only [Schema.noActionTypedAttrs, Bool.and_eq_true, List.all_eq_true] at hnoA
  obtain ⟨hnoEts, hnoActs⟩ := hnoA
  have hfa : full.acts.contains req.action = true := by simp [ActionSchema.contains, hfind]
  subst henv
  refine {
    ets := rfl
    reqty := rfl
    actF := by rw [hacts, hact]; exact hfa
    actS := by
      simp only [hact, ActionSchema.contains, hslice.find?_self, hfind, Option.isSome_some]
    sub := by
      intro u e he
      rw [hacts]; exact (hslice.find?_some he).1
    desc := by
      intro u; simp only [hacts, hact, hslice.descendentOf_eq]
    disj := hwfenvF.2.1.2.2.1
    ancActs := by
      intro u e hm anc hanc
      have hf := Map.mem_toList_find? hwfenvF.2.1.1 hm
      exact (hwfenvF.2.1.2.1 u e hf).2.2.2.2.2.1 anc hanc
    subList := by
      intro u e hm
      have hf := Map.mem_toList_find? hwfenvS.2.1.1 hm
      simp only at hf
      rw [hacts]
      exact Map.find?_mem_toList (hslice.find?_some hf).1
    closureContains := by
      intro u hd
      simp only [hact, hacts] at hd ⊢
      exact hslice.contains_closure (closure_of_descendentOf hfa hd)
    ctx := by
      have haval : ase ∈ full.acts.values := Map.in_list_in_values (Map.find?_mem_toList hfind)
      have := (hnoActs ase haval).1.1
      simp only [Schema.recordMentionsNoActionTypes] at this
      rw [henvF]; exact this
    prin := hpc
    res := hrc
    attrs := by
      intro ety rty hat
      simp only [EntitySchema.attrs?, Option.map_eq_some_iff] at hat
      obtain ⟨entry, hentry, rfl⟩ := hat
      rw [hets] at hentry ⊢
      have hval : entry ∈ full.ets.values := Map.in_list_in_values (Map.find?_mem_toList hentry)
      exact (hnoEts entry hval).1
    tags := by
      intro ety ty htg
      simp only [EntitySchema.tags?, Option.map_eq_some_iff] at htg
      obtain ⟨entry, hentry, htag⟩ := htg
      rw [hets] at hentry ⊢
      have hval : entry ∈ full.ets.values := Map.in_list_in_values (Map.find?_mem_toList hentry)
      have := (hnoEts entry hval).2
      rw [htag] at this
      simpa using this }

/-! ## 7. `evaluatePolicy` decomposition -/

theorem evaluatePolicy_ok_inv {s : Schema} {p : Policy} {req : PartialRequest}
    {es : PartialEntities} {r : Residual} (h : evaluatePolicy s p req es = .ok r) :
    ∃ env te c, validatePartialRequest s req = .ok env ∧ entitiesIsValid env.schema es = true ∧
      checkEntities s p.toExpr = .ok () ∧
      typeOf (substituteAction env.reqty.action p.toExpr) ∅ env = .ok (te, c) ∧
      r = Cedar.TPE.evaluate env te.liftBoolTypes.toResidual req es := by
  unfold evaluatePolicy at h
  split at h
  · rename_i env henv
    split at h
    · rename_i hents
      cases hc : checkEntities s p.toExpr with
      | error e => simp [hc, Except.mapError, bind, Except.bind] at h
      | ok u =>
        simp only [hc, Except.mapError, bind, Except.bind] at h
        split at h
        · cases h
        · rename_i q hq
          split at hq
          · cases hq
          · rename_i q' ht
            simp only [Except.ok.injEq] at hq h
            subst hq
            exact ⟨env, q'.1, q'.2, henv, hents, rfl, ht, h.symm⟩
    · cases h
  · cases h

theorem evaluatePolicy_of {s : Schema} {p : Policy} {req : PartialRequest}
    {es : PartialEntities} {env : TypeEnv} {te : TypedExpr} {c : Capabilities}
    (henv : validatePartialRequest s req = .ok env) (hents : entitiesIsValid env.schema es = true)
    (hc : checkEntities s p.toExpr = .ok ())
    (ht : typeOf (substituteAction env.reqty.action p.toExpr) ∅ env = .ok (te, c)) :
    evaluatePolicy s p req es = .ok (Cedar.TPE.evaluate env te.liftBoolTypes.toResidual req es) := by
  unfold evaluatePolicy
  simp only [henv, hents, ite_true, hc, ht, Except.mapError, bind, Except.bind]

/-! ## 8. Cross-schema evaluation of a kept policy -/

/-- A policy kept by slicing evaluates under the sliced schema to the same
    residual it has under the full schema. -/
theorem evaluatePolicy_kept_cross_schema
    {sliced full : Schema} {policies : Policies} {p p' : Policy}
    {req : PartialRequest} {es : PartialEntities} {envF envS : TypeEnv} {r : Residual}
    (hslice : sliced.IsActionSliceOf full req.action)
    (hwfF : full.validateWellFormed = .ok ())
    (hwfS : sliced.validateWellFormed = .ok ())
    (hmem : p ∈ policies)
    (hnolits : full.noActionLiteralsInConditions policies = true)
    (hnotests : full.noActionTypeTestsInConditions policies = true)
    (hno : full.noActionTypedAttrs = true)
    (hF : validatePartialRequest full req = .ok envF)
    (hS : validatePartialRequest sliced req = .ok envS)
    (hentsS : entitiesIsValid sliced es = true)
    (hsl : Policy.sliceForRequestEnv p envF = some p')
    (hcheckP : checkEntities full p.toExpr = .ok ())
    (hfull : evaluatePolicy full p' req es = .ok r) :
    evaluatePolicy sliced p' req es = .ok r := by
  have h := envRel_of_slice hslice hwfF hwfS hno hF hS
  obtain ⟨env, te, c, henv, _, hc', ht, rfl⟩ := evaluatePolicy_ok_inv hfull
  rw [hF] at henv; cases henv
  have hwfenvF := wf_of_environment hwfF (validatePartialRequest_environment hF).1
  obtain ⟨_, _, hets, hacts, _⟩ := SlicedPoliciesActionInAny.env_facts hF
  have hpiece := h.piece_policy hets hacts hwfenvF hmem hnolits hsl hc'
  obtain ⟨htS, hevS⟩ := hpiece ∅ te c ht
  have hcS := checkEntities_sliced_policy hslice hwfF hmem hnolits hnotests hno hF hsl hcheckP
  have hschS : envS.schema = sliced := by
    obtain ⟨_, _, hetsS, hactsS, _⟩ := SlicedPoliciesActionInAny.env_facts hS
    simp only [TypeEnv.schema, hetsS, hactsS]
  rw [← h.reqty] at htS
  rw [evaluatePolicy_of hS (hschS ▸ hentsS) hcS htS, hevS]

/-! ## 9. Main policy-level theorem -/

/-- Same-schema keep lemma (re-proved here because the original in
    `Cedar.Thm.TPE.SlicedPolicies` is private). -/
theorem evaluatePolicy_slice_keep_same_schema
    {schema : Schema} {p p' : Policy} {req : PartialRequest}
    {es : PartialEntities} {env : TypeEnv} {r : Residual}
    (hreq : validatePartialRequest schema req = .ok env)
    (hents : entitiesIsValid schema es = true)
    (hanc : (es.ancestors req.action).isSome = true)
    (hslice : Policy.sliceForRequestEnv p env = some p')
    (heval : evaluatePolicy schema p req es = .ok r) :
    evaluatePolicy schema p' req es = .ok r := by
  rcases p with ⟨id, effect, ⟨ps⟩, asc, ⟨rs⟩, cs⟩
  cases asc with
  | actionInAny uids =>
    exact SlicedPoliciesActionInAny.evaluatePolicy_actionInAny_slice_keep
      hreq hents hanc hslice rfl heval
  | actionScope actionScope =>
    cases actionScope <;>
      simp only [Policy.sliceForRequestEnv, ActionScope.sliceForAction,
        bind, Option.bind] at hslice
    all_goals
      repeat' split at hslice
      all_goals simp_all

/--
Main result. Under the full-schema baseline (`evaluatePolicy full p = .ok r`),
a policy kept by slicing for the *sliced* request environment evaluates under
the *sliced* schema to exactly the same residual `r`.

`hanc` (the request action's ancestors are known in the partial entities) is
required: without it, an off-closure action scope remains residual under full
partial authorization but policy slicing would drop it as a definite non-match.
-/
theorem evaluatePolicy_sliced_schema_eq_full
    {sliced full : Schema} {policies : Policies} {p p' : Policy}
    {req : PartialRequest} {es : PartialEntities} {envS : TypeEnv} {r : Residual}
    (hwfF : full.validateWellFormed = .ok ())
    (hwfS : sliced.validateWellFormed = .ok ())
    (hslice : sliced.IsActionSliceOf full req.action)
    (hmem : p ∈ policies)
    (hnolits : full.noActionLiteralsInConditions policies = true)
    (hnotests : full.noActionTypeTestsInConditions policies = true)
    (hno : full.noActionTypedAttrs = true)
    (hS : validatePartialRequest sliced req = .ok envS)
    (hentsS : entitiesIsValid sliced es = true)
    (hanc : (es.ancestors req.action).isSome = true)
    (hbase : evaluatePolicy full p req es = .ok r)
    (hsl : Policy.sliceForRequestEnv p envS = some p') :
    evaluatePolicy sliced p' req es = .ok r := by
  obtain ⟨envF, te, c, hF, hentsF, hcheckP, _, _⟩ := evaluatePolicy_ok_inv hbase
  have hschF : envF.schema = full := by
    obtain ⟨_, _, hetsF, hactsF, _⟩ := SlicedPoliciesActionInAny.env_facts hF
    simp only [TypeEnv.schema, hetsF, hactsF]
  have hslF : Policy.sliceForRequestEnv p envF = some p' := by
    rw [sliceForRequestEnv_full_eq_sliced hslice hno hF hS]; exact hsl
  have hfull' : evaluatePolicy full p' req es = .ok r :=
    evaluatePolicy_slice_keep_same_schema hF (hschF ▸ hentsF) hanc hslF hbase
  exact evaluatePolicy_kept_cross_schema hslice hwfF hwfS hmem hnolits hnotests hno hF hS
    hentsS hslF hcheckP hfull'

/-! ## 10. Authorization-level corollary -/

def evalRP (schema : Schema) (p : Policy) (req : PartialRequest) (es : PartialEntities) :
    Except Cedar.TPE.Error ResidualPolicy := do
  pure ⟨p.id, p.effect, ← evaluatePolicy schema p req es⟩

theorem isAuthorized_eq_mapM (schema : Schema) (policies : Policies) (req : PartialRequest)
    (es : PartialEntities) :
    isAuthorized schema policies req es = (do
      let residuals ← policies.mapM (evalRP schema · req es)
      pure (isAuthorizedFromResiduals residuals)) := rfl

/-- Membership-aware version of the list lifting in `SlicedPolicies`. -/
theorem mapM_dropFalse
    {full sliced : Schema} {req : PartialRequest} {es : PartialEntities}
    (slice : Policy → Option Policy) (all : Policies)
    (hdrop : ∀ p ∈ all, ∀ r, slice p = none → evalRP full p req es = .ok r → r.isFalse = true)
    (hkeep : ∀ p ∈ all, ∀ p' r, slice p = some p' → evalRP full p req es = .ok r →
      evalRP sliced p' req es = .ok r) :
    ∀ (policies : Policies), (∀ p ∈ policies, p ∈ all) → ∀ {fullRs : List ResidualPolicy},
    policies.mapM (evalRP full · req es) = .ok fullRs →
    ∃ slicedRs, (policies.filterMap slice).mapM (evalRP sliced · req es) = .ok slicedRs ∧
      ResidualPolicies.DropFalse fullRs slicedRs
  | [], _, fullRs, hfull => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hfull
    subst hfull
    exact ⟨[], rfl, .nil⟩
  | p :: ps, hsub, fullRs, hfull => by
    simp only [List.mapM_cons] at hfull
    have hp_mem := hsub p (List.mem_cons_self ..)
    have hps_sub : ∀ q ∈ ps, q ∈ all := fun q hq => hsub q (List.mem_cons_of_mem _ hq)
    cases hp : evalRP full p req es with
    | error _ => simp [hp, bind, Except.bind] at hfull
    | ok r =>
      simp only [hp, bind, Except.bind] at hfull
      cases hps : ps.mapM (evalRP full · req es) with
      | error e => simp [hps] at hfull
      | ok rs =>
        simp only [hps, pure, Except.pure, Except.ok.injEq] at hfull
        subst fullRs
        obtain ⟨srs, hsrs, hrel⟩ := mapM_dropFalse slice all hdrop hkeep ps hps_sub hps
        cases hsl : slice p with
        | none =>
          simp only [List.filterMap_cons, hsl]
          exact ⟨srs, hsrs, .drop (hdrop p hp_mem r hsl hp) hrel⟩
        | some p' =>
          simp only [List.filterMap_cons, hsl, List.mapM_cons]
          rw [hkeep p hp_mem p' r hsl hp]
          simp only [bind, Except.bind]
          rw [hsrs]
          exact ⟨r :: srs, rfl, .keep hrel⟩

theorem sliceForRequestEnv_preserves_id_effect {p p' : Policy} {env : TypeEnv}
    (h : Policy.sliceForRequestEnv p env = some p') : p'.id = p.id ∧ p'.effect = p.effect := by
  obtain ⟨_, _, _, _, rfl⟩ := sliceForRequestEnv_facts h
  exact ⟨rfl, rfl⟩

/-- Authorization with sliced policies under the sliced schema refines full
    authorization under the full schema. -/
theorem isAuthorized_sliced_schema_refines
    {sliced full : Schema} {policies : Policies}
    {req : PartialRequest} {es : PartialEntities} {envS : TypeEnv} {rf : Cedar.TPE.Response}
    (hwfF : full.validateWellFormed = .ok ())
    (hwfS : sliced.validateWellFormed = .ok ())
    (hslice : sliced.IsActionSliceOf full req.action)
    (hnolits : full.noActionLiteralsInConditions policies = true)
    (hnotests : full.noActionTypeTestsInConditions policies = true)
    (hno : full.noActionTypedAttrs = true)
    (hS : validatePartialRequest sliced req = .ok envS)
    (hentsS : entitiesIsValid sliced es = true)
    (hanc : (es.ancestors req.action).isSome = true)
    (hbase : isAuthorized full policies req es = .ok rf) :
    ∃ rs, isAuthorized sliced (slicePoliciesForRequestEnv policies envS) req es = .ok rs ∧
      rs.SliceRefines rf := by
  have evalRP_ok : ∀ {s p rp}, evalRP s p req es = .ok rp →
      ∃ r, evaluatePolicy s p req es = .ok r ∧ rp = ⟨p.id, p.effect, r⟩ := by
    intro s p rp h
    simp only [evalRP] at h
    cases he : evaluatePolicy s p req es with
    | error e => simp [he, bind, Except.bind] at h
    | ok r =>
      simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨r, rfl, h.symm⟩
  have hdrop : ∀ p ∈ policies, ∀ rp, Policy.sliceForRequestEnv p envS = none →
      evalRP full p req es = .ok rp → rp.isFalse = true := by
    intro p _ rp hsl hrp
    obtain ⟨r, hr, rfl⟩ := evalRP_ok hrp
    obtain ⟨envF, _, _, hF, _, _, _, _⟩ := evaluatePolicy_ok_inv hr
    have hslF : Policy.sliceForRequestEnv p envF = none := by
      rw [sliceForRequestEnv_full_eq_sliced hslice hno hF hS]; exact hsl
    exact SlicedPoliciesDropped.evaluatePolicy_dropped_isFalse hF hanc hslF hr
  have hkeep : ∀ p ∈ policies, ∀ p' rp, Policy.sliceForRequestEnv p envS = some p' →
      evalRP full p req es = .ok rp → evalRP sliced p' req es = .ok rp := by
    intro p hmem p' rp hsl hrp
    obtain ⟨r, hr, rfl⟩ := evalRP_ok hrp
    have := evaluatePolicy_sliced_schema_eq_full hwfF hwfS hslice hmem hnolits hnotests hno hS
      hentsS hanc hr hsl
    obtain ⟨hid, heff⟩ := sliceForRequestEnv_preserves_id_effect hsl
    simp only [evalRP, this, bind, Except.bind, pure, Except.pure, hid, heff]
  rw [isAuthorized_eq_mapM] at hbase ⊢
  cases hfull : policies.mapM (evalRP full · req es) with
  | error _ => simp [hfull, bind, Except.bind] at hbase
  | ok fullRs =>
    simp only [hfull, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hbase
    subst rf
    obtain ⟨srs, hsrs, hrel⟩ := mapM_dropFalse (Policy.sliceForRequestEnv · envS) policies
      hdrop hkeep policies (fun _ h => h) hfull
    simp only [slicePoliciesForRequestEnv]
    rw [hsrs]
    exact ⟨isAuthorizedFromResiduals srs, rfl, isAuthorizedFromResiduals_dropFalse hrel⟩

/-- The executable wrapper, run on the sliced schema, refines full-schema
    partial authorization whenever its own entity/ancestor guard passes. -/
theorem isAuthorizedPartialWithSlicedPolicies_refines_full
    {sliced full : Schema} {policies : Policies}
    {req : PartialRequest} {es : PartialEntities} {envS : TypeEnv} {rf : Cedar.TPE.Response}
    (hwfF : full.validateWellFormed = .ok ())
    (hwfS : sliced.validateWellFormed = .ok ())
    (hslice : sliced.IsActionSliceOf full req.action)
    (hnolits : full.noActionLiteralsInConditions policies = true)
    (hnotests : full.noActionTypeTestsInConditions policies = true)
    (hno : full.noActionTypedAttrs = true)
    (hS : validatePartialRequest sliced req = .ok envS)
    (hguard : (entitiesIsValid envS.schema es && (es.ancestors req.action).isSome) = true)
    (hbase : isAuthorized full policies req es = .ok rf) :
    ∃ rs, isAuthorizedPartialWithSlicedPolicies sliced policies req es = .ok rs ∧
      rs.SliceRefines rf := by
  have hschS : envS.schema = sliced := by
    obtain ⟨_, _, hetsS, hactsS, _⟩ := SlicedPoliciesActionInAny.env_facts hS
    simp only [TypeEnv.schema, hetsS, hactsS]
  simp only [Bool.and_eq_true] at hguard
  obtain ⟨hents, hanc⟩ := hguard
  unfold isAuthorizedPartialWithSlicedPolicies
  simp only [hS, hents, hanc, Bool.and_self, ite_true]
  exact isAuthorized_sliced_schema_refines hwfF hwfS hslice hnolits hnotests hno hS
    (hschS ▸ hents) hanc hbase

end Cedar.Thm.CrossSchema
