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
import Cedar.Thm.Data

namespace Cedar.Thm.SlicedPoliciesActionInAny

open Cedar.Data Cedar.Spec Cedar.Validation Cedar.TPE

def lits (us : List EntityUID) : List Expr := us.map fun u => Expr.lit (.entityUID u)

theorem lits_cons (u : EntityUID) (us : List EntityUID) :
    lits (u :: us) = .lit (.entityUID u) :: lits us := rfl

theorem subst_actionInAny (a : EntityUID) (us : List EntityUID) :
    substituteAction a (ActionScope.actionInAny us).toExpr =
      .binaryApp .mem (.lit (.entityUID a)) (.set (lits us)) := by
  simp only [substituteAction, ActionScope.toExpr, mapOnVars]
  congr 2
  rw [List.map₁_eq_map (fun x => mapOnVars _ x)]
  simp only [lits, List.map_map]
  congr 1
  funext u
  simp [mapOnVars]

theorem entityUIDs?_lits (us : List EntityUID) : entityUIDs? (.set (lits us)) = some us := by
  simp only [entityUIDs?]
  induction us with
  | nil => rfl
  | cons u us ih =>
    rw [lits_cons, List.mapM_cons, ih]
    rfl

abbrev typedLits (us : List EntityUID) : List TypedExpr :=
  us.map fun u => TypedExpr.lit (.entityUID u) (.entity u.ty)

abbrev validUID (env : TypeEnv) (u : EntityUID) : Bool :=
  env.ets.isValidEntityUID u || env.acts.contains u

theorem justType_lit (u : EntityUID) (c : Capabilities) (env : TypeEnv) :
    justType (typeOf (.lit (.entityUID u)) c env) =
      if validUID env u then .ok (TypedExpr.lit (.entityUID u) (.entity u.ty))
      else .error (.unknownEntity u.ty) := by
  simp only [typeOf, typeOfLit, justType, validUID]
  split <;> rfl

theorem mapM_lits_ok {us : List EntityUID} {c : Capabilities} {env : TypeEnv} {tys : List TypedExpr}
    (h : (lits us).mapM (fun x => justType (typeOf x c env)) = .ok tys) :
    tys = typedLits us ∧ ∀ u ∈ us, validUID env u = true := by
  induction us generalizing tys with
  | nil => simp_all [lits, pure, Except.pure]
  | cons u us ih =>
    rw [lits_cons, List.mapM_cons, justType_lit] at h
    split at h
    · cases hm : List.mapM (fun x => justType (typeOf x c env)) (lits us) with
      | error e => simp [hm, bind, Except.bind] at h
      | ok tys' =>
        simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨h1, h2⟩ := ih hm
        subst h h1
        refine ⟨rfl, ?_⟩
        intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · assumption
        · exact h2 v hv
    · simp [bind, Except.bind] at h

theorem mapM_lits_of_valid {us : List EntityUID} {c : Capabilities} {env : TypeEnv}
    (h : ∀ u ∈ us, validUID env u = true) :
    (lits us).mapM (fun x => justType (typeOf x c env)) = .ok (typedLits us) := by
  induction us with
  | nil => simp [lits, pure, Except.pure]
  | cons u us ih =>
    rw [lits_cons, List.mapM_cons, justType_lit, ite_eq_left (h u (by simp)),
      ih (fun v hv => h v (by simp [hv]))]
    rfl

theorem foldl_lub_entity (e : EntityType) (tl : List EntityUID) (ty : CedarType)
    (h : (tl.map fun u => CedarType.entity u.ty).foldlM lub? (.entity e) = some ty) :
    ty = .entity e ∧ ∀ u ∈ tl, u.ty = e := by
  induction tl with
  | nil => simp_all [pure]
  | cons u tl ih =>
    simp only [List.map_cons, List.foldlM_cons] at h
    by_cases he : u.ty = e
    · subst he
      simp only [lub?, ite_true, bind, Option.bind] at h
      obtain ⟨h1, h2⟩ := ih h
      refine ⟨h1, ?_⟩
      intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · rfl
      · exact h2 v hv
    · have : CedarType.entity e ≠ CedarType.entity u.ty := by
        intro h'; cases h'; exact he rfl
      simp [lub?, this, bind, Option.bind] at h

theorem foldl_lub_entity_of (e : EntityType) (tl : List EntityUID)
    (h : ∀ u ∈ tl, u.ty = e) :
    (tl.map fun u => CedarType.entity u.ty).foldlM lub? (.entity e) = some (.entity e) := by
  induction tl with
  | nil => rfl
  | cons u tl ih =>
    simp only [List.map_cons, List.foldlM_cons]
    rw [h u (by simp)]
    simp only [lub?, ite_true, bind, Option.bind]
    exact ih (fun v hv => h v (by simp [hv]))

theorem typeOfSet_typedLits {us : List EntityUID} {t : TypedExpr} {c : Capabilities}
    (h : typeOfSet (typedLits us) = .ok (t, c)) :
    ∃ e, us ≠ [] ∧ (∀ u ∈ us, u.ty = e) ∧ c = ∅ ∧
      t = .set (typedLits us) (.set (.entity e)) := by
  cases us with
  | nil => simp [typeOfSet, err] at h
  | cons u us =>
    simp only [typeOfSet, typedLits, List.map_cons, List.map_map] at h
    split at h
    · rename_i ty hty
      have hty' : (us.map fun u => CedarType.entity u.ty).foldlM lub? (.entity u.ty) = some ty := by
        simpa [Function.comp_def, TypedExpr.typeOf] using hty
      obtain ⟨h1, h2⟩ := foldl_lub_entity _ _ _ hty'
      subst h1
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h3, h4⟩ := h
      refine ⟨u.ty, by simp, ?_, h4.symm, ?_⟩
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · rfl
        · exact h2 v hv
      · rw [← h3]; rfl
    · simp [err] at h

theorem typeOfSet_typedLits_of {us : List EntityUID} {e : EntityType}
    (hne : us ≠ []) (h : ∀ u ∈ us, u.ty = e) :
    typeOfSet (typedLits us) = .ok (.set (typedLits us) (.set (.entity e)), ∅) := by
  cases us with
  | nil => exact absurd rfl hne
  | cons u us =>
    have hu : u.ty = e := h u (by simp)
    have hf := foldl_lub_entity_of u.ty us (fun v hv => (h v (by simp [hv])).trans hu.symm)
    simp only [typeOfSet, typedLits, List.map_cons, List.map_map]
    have hf' : ((us.map fun u => TypedExpr.lit (.entityUID u) (.entity u.ty)).map TypedExpr.typeOf).foldlM
        lub? (TypedExpr.lit (.entityUID u) (.entity u.ty)).typeOf = some (.entity u.ty) := by
      simpa [Function.comp_def, TypedExpr.typeOf] using hf
    simp only [List.map_map] at hf'
    rw [hf']
    subst hu
    rfl

abbrev actExpr (a : EntityUID) (us : List EntityUID) : Expr :=
  .binaryApp .mem (.lit (.entityUID a)) (.set (lits us))

abbrev actTyped (a : EntityUID) (us : List EntityUID) (e : EntityType) (b : BoolType) : TypedExpr :=
  .binaryApp .mem (.lit (.entityUID a) (.entity a.ty)) (.set (typedLits us) (.set (.entity e))) (.bool b)

theorem typeOf_set_lits (us : List EntityUID) (c : Capabilities) (env : TypeEnv) :
    typeOf (.set (lits us)) c env =
      ((lits us).mapM (fun x => justType (typeOf x c env)) >>= typeOfSet) := by
  simp only [typeOf]
  rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))]

theorem typeOf_actExpr {a : EntityUID} {us : List EntityUID} {c cA : Capabilities}
    {env : TypeEnv} {tA : TypedExpr}
    (hact : env.acts.contains a = true)
    (h : typeOf (actExpr a us) c env = .ok (tA, cA)) :
    ∃ e, us ≠ [] ∧ (∀ u ∈ us, validUID env u = true ∧ u.ty = e) ∧ cA = ∅ ∧
      tA = actTyped a us e (if us.any (env.acts.descendentOf a ·) then .tt else .ff) := by
  have hlit : typeOfLit (.entityUID a) env =
      .ok (TypedExpr.lit (.entityUID a) (.entity a.ty), ∅) := by
    simp [typeOfLit, hact, ok]
  simp only [actExpr, typeOf] at h
  rw [hlit, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
  cases hm : (lits us).mapM (fun x => justType (typeOf x c env)) with
  | error e => simp [hm, bind, Except.bind] at h
  | ok tys =>
    obtain ⟨rfl, hv⟩ := mapM_lits_ok hm
    simp only [hm, bind, Except.bind] at h
    cases hs : typeOfSet (typedLits us) with
    | error e => simp [hs] at h
    | ok r =>
      obtain ⟨tS, cS⟩ := r
      obtain ⟨e, hne, hty, rfl, rfl⟩ := typeOfSet_typedLits hs
      simp only [hs] at h
      simp [typeOfBinaryApp, TypedExpr.typeOf, typeOfInₛ, actionUID?, entityUID?, hact,
        entityUIDs?_lits, ok] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨e, hne, fun u hu => ⟨hv u hu, hty u hu⟩, rfl, by simp [actTyped]⟩

theorem typeOf_actExpr_of {a : EntityUID} {us : List EntityUID} {c : Capabilities}
    {env : TypeEnv} {e : EntityType}
    (hact : env.acts.contains a = true) (hne : us ≠ [])
    (hv : ∀ u ∈ us, validUID env u = true ∧ u.ty = e) :
    typeOf (actExpr a us) c env =
      .ok (actTyped a us e (if us.any (env.acts.descendentOf a ·) then .tt else .ff), ∅) := by
  have hlit : typeOfLit (.entityUID a) env =
      .ok (TypedExpr.lit (.entityUID a) (.entity a.ty), ∅) := by
    simp [typeOfLit, hact, ok]
  simp only [actExpr, typeOf]
  rw [hlit, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)), mapM_lits_of_valid (fun u hu => (hv u hu).1)]
  simp only [bind, Except.bind]
  rw [typeOfSet_typedLits_of hne (fun u hu => (hv u hu).2)]
  simp [typeOfBinaryApp, TypedExpr.typeOf, typeOfInₛ, actionUID?, entityUID?, hact,
    entityUIDs?_lits, ok]

theorem mapM_asValue_vals (us : List EntityUID) :
    List.mapM Residual.asValue (us.map fun x => Residual.val (Value.prim (Prim.entityUID x)) (CedarType.entity x.ty)) =
      some (us.map fun x => Value.prim (Prim.entityUID x)) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    rw [List.map_cons, List.mapM_cons, ih]
    rfl

theorem apply₂_mem_val (env : TypeEnv) (es : PartialEntities) (a : EntityUID) (e : EntityType)
    (S : Set Value) (ty : CedarType) (h : inₛ a S es = some true) :
    apply₂ env .mem (.val (.prim (.entityUID a)) (.entity a.ty)) (.val (.set S) (.set (.entity e))) es ty =
      .val (if env.descendentOf a.ty e then true else false) ty := by
  simp [Cedar.TPE.apply₂, tryDecideResidual₂, Residual.errorFree, Residual.typeOf, Residual.asValue, someOrSelf, h]
  cases env.descendentOf a.ty e <;> rfl

theorem eval_actTyped (env : TypeEnv) (req : PartialRequest) (es : PartialEntities)
    (a : EntityUID) (us : List EntityUID) (e : EntityType) (b : BoolType)
    (h : inₛ a (Set.make (us.map fun x => Value.prim (Prim.entityUID x))) es = some true) :
    Cedar.TPE.evaluate env (actTyped a us e b).liftBoolTypes.toResidual req es =
      .val (if env.descendentOf a.ty e then true else false) (.bool b.lift) := by
  simp [actTyped, TypedExpr.liftBoolTypes, TypedExpr.toResidual, CedarType.liftBoolTypes, Cedar.TPE.evaluate,
    List.map₁_eq_map, typedLits, List.map_map, Function.comp_def, Cedar.TPE.set]
  rw [List.map₁_eq_map (fun x => Cedar.TPE.evaluate env x req es)]
  simp only [List.map_map, Function.comp_def, Cedar.TPE.evaluate]
  rw [mapM_asValue_vals]
  exact apply₂_mem_val env es a e _ _ h

theorem mapM_asEntityUID (ws : List Value)
    (h : ∀ w ∈ ws, ∃ u, w = Value.prim (Prim.entityUID u)) :
    ∃ L, ws.mapM (Except.toOption ∘ Value.asEntityUID) = some L ∧
      ∀ u, Value.prim (Prim.entityUID u) ∈ ws → u ∈ L := by
  induction ws with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons w ws ih =>
    obtain ⟨u, rfl⟩ := h w (by simp)
    obtain ⟨L, hL, hmem⟩ := ih (fun w hw => h w (by simp [hw]))
    refine ⟨u :: L, ?_, ?_⟩
    · rw [List.mapM_cons, hL]
      rfl
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with hv | hv
      · cases hv; simp
      · exact List.mem_cons_of_mem _ (hmem v hv)

theorem inₛ_make_true (a : EntityUID) (us : List EntityUID) (es : PartialEntities)
    (h : ∃ u ∈ us, Cedar.TPE.inₑ a u es = some true) :
    inₛ a (Set.make (us.map fun x => Value.prim (Prim.entityUID x))) es = some true := by
  obtain ⟨L, hL, hmem⟩ := mapM_asEntityUID
    (Set.make (us.map fun x => Value.prim (Prim.entityUID x))).toList (by
      intro w hw
      have : w ∈ Set.make (us.map fun x => Value.prim (Prim.entityUID x)) := hw
      rw [Set.mem_make] at this
      simp only [List.mem_map] at this
      obtain ⟨u, _, rfl⟩ := this
      exact ⟨u, rfl⟩)
  obtain ⟨u, hu, hin⟩ := h
  have huL : u ∈ L := by
    apply hmem
    show _ ∈ Set.make _
    rw [Set.mem_make]
    exact List.mem_map_of_mem hu
  simp only [Cedar.TPE.inₛ, hL, bind, Option.bind, List.ternaryAny]
  have : (L.map (Cedar.TPE.inₑ a · es)).any (· == some true) = true := by
    simp only [List.any_map, List.any_eq_true, Function.comp_def]
    exact ⟨u, huL, by simp [hin]⟩
  simp [this]

theorem typeOf_and' (x₁ x₂ : Expr) (c : Capabilities) (env : TypeEnv) :
    typeOf (.and x₁ x₂) c env = (do
      let (ty₁, c₁) ← typeOf x₁ c env
      typeOfAnd (ty₁, c₁) (typeOf x₂ (c ∪ c₁) env)) := by
  rw [typeOf]

def ev (env : TypeEnv) (req : PartialRequest) (es : PartialEntities) (t : TypedExpr) : Residual :=
  Cedar.TPE.evaluate env t.liftBoolTypes.toResidual req es

def Rel (env : TypeEnv) (req : PartialRequest) (es : PartialEntities) (r₁ r₂ : ResultType) : Prop :=
  ∀ t c, r₁ = .ok (t, c) → ∃ t', r₂ = .ok (t', c) ∧ t'.typeOf = t.typeOf ∧ ev env req es t' = ev env req es t

theorem ev_and (env : TypeEnv) (req : PartialRequest) (es : PartialEntities) (x y : TypedExpr) (ty : CedarType) :
    ev env req es (.and x y ty) = Cedar.TPE.and (ev env req es x) (ev env req es y) ty.liftBoolTypes := by
  simp only [ev, TypedExpr.liftBoolTypes, TypedExpr.toResidual]
  rw [Cedar.TPE.evaluate]

theorem typeOfAnd_r₂ {t₁ t₁' : TypedExpr} {c₁ c : Capabilities} {r₂ r₂' : ResultType} {b : BoolType}
    {env : TypeEnv} {req : PartialRequest} {es : PartialEntities} {t : TypedExpr}
    (hev : ev env req es t₁' = ev env req es t₁)
    (hrel : Rel env req es r₂ r₂')
    (h : (do
      let __x ← r₂
      match __x.fst.typeOf with
        | CedarType.bool BoolType.ff => ok (t₁.and __x.fst (CedarType.bool BoolType.ff))
        | CedarType.bool BoolType.tt => ok (t₁.and __x.fst (CedarType.bool b)) (c₁ ∪ __x.snd)
        | CedarType.bool _ => ok (t₁.and __x.fst (CedarType.bool BoolType.anyBool)) (c₁ ∪ __x.snd)
        | _ => err (TypeError.unexpectedType __x.fst.typeOf) : ResultType) = .ok (t, c)) :
    ∃ t', (do
      let __x ← r₂'
      match __x.fst.typeOf with
        | CedarType.bool BoolType.ff => ok (t₁'.and __x.fst (CedarType.bool BoolType.ff))
        | CedarType.bool BoolType.tt => ok (t₁'.and __x.fst (CedarType.bool b)) (c₁ ∪ __x.snd)
        | CedarType.bool _ => ok (t₁'.and __x.fst (CedarType.bool BoolType.anyBool)) (c₁ ∪ __x.snd)
        | _ => err (TypeError.unexpectedType __x.fst.typeOf) : ResultType) = .ok (t', c) ∧
      t'.typeOf = t.typeOf ∧ ev env req es t' = ev env req es t := by
  cases hr : r₂ with
  | error e => simp [hr, bind, Except.bind] at h
  | ok r =>
    obtain ⟨ty₂, c₂⟩ := r
    obtain ⟨ty₂', hr', hty, hev₂⟩ := hrel ty₂ c₂ hr
    simp only [hr, hr', bind, Except.bind, hty] at h ⊢
    split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;>
      exact ⟨_, rfl, rfl, by rw [ev_and, ev_and, hev, hev₂]⟩

theorem Rel_refl {env : TypeEnv} {req : PartialRequest} {es : PartialEntities} (r : ResultType) :
    Rel env req es r r := fun t _ h => ⟨t, h, rfl, rfl⟩

theorem typeOfAnd_congr {t₁ t₂ : TypedExpr} {c₁ : Capabilities} {r₂ r₂' : ResultType}
    {env : TypeEnv} {req : PartialRequest} {es : PartialEntities}
    (hty : t₂.typeOf = t₁.typeOf) (hev : ev env req es t₂ = ev env req es t₁)
    (hrel : Rel env req es r₂ r₂') :
    Rel env req es (typeOfAnd (t₁, c₁) r₂) (typeOfAnd (t₂, c₁) r₂') := by
  intro t c h
  unfold typeOfAnd at h ⊢
  simp only [hty]
  generalize t₁.typeOf = T at h ⊢
  cases T
  case bool b =>
    cases b
    · exact typeOfAnd_r₂ hev hrel h
    · exact typeOfAnd_r₂ hev hrel h
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨t₂, rfl, hty, hev⟩
  all_goals simp [err] at h

theorem typeOf_and_congr_left {A₁ A₂ Y : Expr} {c : Capabilities}
    {env : TypeEnv} {req : PartialRequest} {es : PartialEntities}
    (hrel : Rel env req es (typeOf A₁ c env) (typeOf A₂ c env)) :
    Rel env req es (typeOf (.and A₁ Y) c env) (typeOf (.and A₂ Y) c env) := by
  intro t c' h
  rw [typeOf_and'] at h ⊢
  cases h₁ : typeOf A₁ c env with
  | error e => simp [h₁, bind, Except.bind] at h
  | ok r =>
    obtain ⟨t₁, c₁⟩ := r
    obtain ⟨t₂, h₂, hty, hev⟩ := hrel t₁ c₁ h₁
    simp only [h₁, h₂, bind, Except.bind] at h ⊢
    exact typeOfAnd_congr hty hev (Rel_refl _) t c' h

theorem typeOf_and_congr_right {P Z₁ Z₂ : Expr} {c : Capabilities}
    {env : TypeEnv} {req : PartialRequest} {es : PartialEntities}
    (hrel : ∀ c', Rel env req es (typeOf Z₁ c' env) (typeOf Z₂ c' env)) :
    Rel env req es (typeOf (.and P Z₁) c env) (typeOf (.and P Z₂) c env) := by
  intro t c' h
  rw [typeOf_and'] at h ⊢
  cases h₁ : typeOf P c env with
  | error e => simp [h₁, bind, Except.bind] at h
  | ok r =>
    obtain ⟨t₁, c₁⟩ := r
    simp only [h₁, bind, Except.bind] at h ⊢
    exact typeOfAnd_congr rfl rfl (hrel _) t c' h

theorem rel_actExpr {env : TypeEnv} {req : PartialRequest} {es : PartialEntities}
    {a : EntityUID} {uids kept : List EntityUID}
    (hact : env.acts.contains a = true)
    (hsub : ∀ u ∈ kept, u ∈ uids) (hne : kept ≠ [])
    (hdesc : ∀ u ∈ kept, env.acts.descendentOf a u = true)
    (hin : ∀ u, env.acts.descendentOf a u = true → Cedar.TPE.inₑ a u es = some true)
    (c : Capabilities) :
    Rel env req es (typeOf (actExpr a uids) c env) (typeOf (actExpr a kept) c env) := by
  intro t c' h
  obtain ⟨e, _, hv, rfl, rfl⟩ := typeOf_actExpr hact h
  obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil kept hne
  have hanyU : (uids.any (env.acts.descendentOf a ·)) = true :=
    List.any_eq_true.mpr ⟨k, hsub k hk, hdesc k hk⟩
  have hanyK : (kept.any (env.acts.descendentOf a ·)) = true :=
    List.any_eq_true.mpr ⟨k, hk, hdesc k hk⟩
  refine ⟨_, typeOf_actExpr_of hact hne (fun u hu => hv u (hsub u hu)), ?_, ?_⟩
  · simp only [hanyU, hanyK]; rfl
  · simp only [ev, hanyU, hanyK]
    rw [eval_actTyped _ _ _ _ _ _ _ (inₛ_make_true _ _ _ ⟨k, hk, hin k (hdesc k hk)⟩),
      eval_actTyped _ _ _ _ _ _ _ (inₛ_make_true _ _ _ ⟨k, hsub k hk, hin k (hdesc k hk)⟩)]

theorem subst_and (a : EntityUID) (x y : Expr) :
    substituteAction a (.and x y) = .and (substituteAction a x) (substituteAction a y) := by
  simp only [substituteAction]
  rw [mapOnVars]

theorem check_and (schema : Schema) (x y : Expr) :
    checkEntities schema (.and x y) = .ok () ↔
      checkEntities schema x = .ok () ∧ checkEntities schema y = .ok () := by
  rw [checkEntities]
  cases checkEntities schema x <;> simp [bind, Except.bind]

theorem check_actionInAny {schema : Schema} {uids kept : List EntityUID}
    (hsub : ∀ u ∈ kept, u ∈ uids)
    (h : checkEntities schema (ActionScope.actionInAny uids).toExpr = .ok ()) :
    checkEntities schema (ActionScope.actionInAny kept).toExpr = .ok () := by
  have hset : ∀ us : List EntityUID, (ActionScope.actionInAny us).toExpr =
      .binaryApp .mem (.var .action) (.set (lits us)) := fun _ => rfl
  rw [hset] at h ⊢
  rw [checkEntities] at h ⊢
  simp only [checkEntities, bind, Except.bind] at h ⊢
  apply List.all_ok_implies_forM_ok
  intro x _
  have hall := List.forM_ok_implies_all_ok _ _ h
  have hx : x.val ∈ lits uids := by
    have := x.property
    simp only [lits, List.mem_map] at this ⊢
    obtain ⟨u, hu, hux⟩ := this
    exact ⟨u, hsub u hu, hux⟩
  exact hall ⟨x.val, hx⟩ (List.mem_attach _ _)

theorem env_facts {schema : Schema} {req : PartialRequest} {env : TypeEnv}
    (h : validatePartialRequest schema req = .ok env) :
    ∃ ase, schema.acts.find? req.action = some ase ∧ env.ets = schema.ets ∧
      env.acts = schema.acts ∧ env.reqty.action = req.action := by
  unfold validatePartialRequest at h
  split at h
  · rename_i env' henv
    split at h
    · cases h
      unfold Schema.environment? at henv
      cases hf : schema.acts.find? req.action with
      | none => simp [hf] at henv
      | some ase =>
        simp only [hf, bind, Option.bind] at henv
        split at henv
        · cases henv
          exact ⟨ase, rfl, rfl, rfl, rfl⟩
        · cases henv
    · cases h
  · cases h

theorem slice_facts {p p' : Policy} {env : TypeEnv} {uids : List EntityUID}
    (hscope : p.actionScope = .actionInAny uids)
    (h : Policy.sliceForRequestEnv p env = some p') :
    p' = { p with actionScope := .actionInAny (uids.filter (env.acts.descendentOf env.reqty.action ·)) } ∧
      uids.filter (env.acts.descendentOf env.reqty.action ·) ≠ [] := by
  unfold Policy.sliceForRequestEnv at h
  simp only [hscope, ActionScope.sliceForAction] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hne
      simp only [bind, Option.bind] at h
      split at h
      · cases h
      · cases h
        refine ⟨rfl, ?_⟩
        simpa using hne

theorem ancestors_eq {schema : Schema} {es : PartialEntities} {a : EntityUID}
    {ase : ActionSchemaEntry} {ancs : Set EntityUID}
    (hes : entitiesIsValid schema es = true)
    (hfind : schema.acts.find? a = some ase)
    (hanc : es.ancestors a = some ancs) :
    ancs = ase.ancestors := by
  simp only [entitiesIsValid, Bool.and_eq_true, List.all_eq_true] at hes
  have h := hes.2 (a, ase) (Map.find?_mem_toList hfind)
  simp only [entitiesIsValid.instanceOfActionSchema] at h
  simp only [PartialEntities.ancestors, PartialEntities.get] at hanc
  cases hd : es.find? a with
  | none => simp [hd] at hanc
  | some d =>
    simp only [hd, Option.bind_some] at hanc
    simp only [hd, entitiesIsValid.actionEntityIsValid, hfind, partialIsValid, hanc,
      Option.map_some, Option.getD_some, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.symm

theorem inₑ_of_descendentOf {schema : Schema} {es : PartialEntities} {a u : EntityUID}
    {ase : ActionSchemaEntry}
    (hes : entitiesIsValid schema es = true)
    (hfind : schema.acts.find? a = some ase)
    (hanc : (es.ancestors a).isSome = true)
    (hdesc : schema.acts.descendentOf a u = true) :
    Cedar.TPE.inₑ a u es = some true := by
  unfold Cedar.TPE.inₑ
  by_cases hau : a = u
  · simp [hau]
  · simp only [hau, ite_false]
    obtain ⟨ancs, hancs⟩ := Option.isSome_iff_exists.mp hanc
    have := ancestors_eq hes hfind hancs
    subst this
    simp only [ActionSchema.descendentOf, hfind] at hdesc
    have hau' : (a == u) = false := by simp [hau]
    simp only [hau', Bool.false_eq_true, ite_false] at hdesc
    simp [hancs, hdesc]

theorem policy_toExpr_subst (a : EntityUID) (p : Policy) :
    substituteAction a p.toExpr =
      .and (substituteAction a p.principalScope.toExpr)
        (.and (substituteAction a p.actionScope.toExpr)
          (.and (substituteAction a p.resourceScope.toExpr)
            (substituteAction a p.condition.toExpr))) := by
  simp only [Policy.toExpr, subst_and]

theorem policy_toExpr_check (schema : Schema) (p : Policy) :
    checkEntities schema p.toExpr = .ok () ↔
      checkEntities schema p.principalScope.toExpr = .ok () ∧
      checkEntities schema p.actionScope.toExpr = .ok () ∧
      checkEntities schema p.resourceScope.toExpr = .ok () ∧
      checkEntities schema p.condition.toExpr = .ok () := by
  simp only [Policy.toExpr, check_and]

/-- For an `action in [...]` policy, slicing for the request environment
    preserves the TPE residual of the policy. -/
theorem evaluatePolicy_actionInAny_slice_keep
    {schema : Schema} {req : PartialRequest} {es : PartialEntities} {env : TypeEnv}
    {p p' : Policy} {uids : List EntityUID} {r : Residual}
    (hreq : validatePartialRequest schema req = .ok env)
    (hes : entitiesIsValid schema es = true)
    (hanc : (es.ancestors req.action).isSome = true)
    (hslice : Policy.sliceForRequestEnv p env = some p')
    (hscope : p.actionScope = .actionInAny uids)
    (heval : evaluatePolicy schema p req es = .ok r) :
    evaluatePolicy schema p' req es = .ok r := by
  obtain ⟨ase, hfind, hets, hacts, hact⟩ := env_facts hreq
  obtain ⟨rfl, hne⟩ := slice_facts hscope hslice
  have hsch : env.schema = schema := by
    simp only [TypeEnv.schema, hets, hacts]
  have hcontains : env.acts.contains env.reqty.action = true := by
    rw [hacts, hact]
    simp [ActionSchema.contains, hfind]
  have hin : ∀ u, env.acts.descendentOf env.reqty.action u = true →
      Cedar.TPE.inₑ env.reqty.action u es = some true := by
    intro u hu
    rw [hact] at hu ⊢
    rw [hacts] at hu
    exact inₑ_of_descendentOf hes hfind hanc hu
  generalize hkept : uids.filter (env.acts.descendentOf env.reqty.action ·) = kept at hne
  have hsub : ∀ u ∈ kept, u ∈ uids := by
    intro u hu; rw [← hkept] at hu; exact (List.mem_filter.mp hu).1
  have hdesc : ∀ u ∈ kept, env.acts.descendentOf env.reqty.action u = true := by
    intro u hu; rw [← hkept] at hu; simpa using (List.mem_filter.mp hu).2
  unfold evaluatePolicy at heval ⊢
  rw [hreq] at heval ⊢
  simp only [hsch, hes, ite_true] at heval ⊢
  cases hc : checkEntities schema p.toExpr with
  | error e => simp [hc, Except.mapError, bind, Except.bind] at heval
  | ok u =>
    have hc' : checkEntities schema p.toExpr = .ok () := hc
    have hc'' : checkEntities schema
        ({ p with actionScope := ActionScope.actionInAny kept } : Policy).toExpr = .ok () := by
      rw [policy_toExpr_check] at hc' ⊢
      refine ⟨hc'.1, ?_, hc'.2.2⟩
      rw [hscope] at hc'
      exact check_actionInAny hsub hc'.2.1
    cases ht : typeOf (substituteAction env.reqty.action p.toExpr) ∅ env with
    | error e => simp only [hc, ht, Except.mapError, bind, Except.bind] at heval; cases heval
    | ok tc =>
      obtain ⟨te, cte⟩ := tc
      simp only [hc, hc'', ht, Except.mapError, bind, Except.bind, Except.ok.injEq] at heval ⊢
      subst heval
      have hrel : Rel env req es (typeOf (substituteAction env.reqty.action p.toExpr) ∅ env)
          (typeOf (substituteAction env.reqty.action
            ({ p with actionScope := ActionScope.actionInAny kept } : Policy).toExpr) ∅ env) := by
        rw [policy_toExpr_subst, policy_toExpr_subst]
        simp only [hscope]
        rw [subst_actionInAny, subst_actionInAny]
        exact typeOf_and_congr_right (fun c' =>
          typeOf_and_congr_left (rel_actExpr hcontains hsub hne hdesc hin c'))
      obtain ⟨te', ht', _, hev⟩ := hrel te cte ht
      simp only [ht']
      exact congrArg Except.ok hev

end Cedar.Thm.SlicedPoliciesActionInAny
