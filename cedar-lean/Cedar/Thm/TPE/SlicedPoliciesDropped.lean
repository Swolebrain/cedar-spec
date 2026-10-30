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

/-
 Dropped policies are literally false.

 Main result: `DroppedPolicy.evaluatePolicy_dropped_isFalse`.

 If `validatePartialRequest schema req = .ok env`,
    `Policy.sliceForRequestEnv p env = none`, and
    `evaluatePolicy schema p req es = .ok r`,
 then `r.isFalse = true`, PROVIDED the request action's ancestors are known in
 `es`, i.e. `(es.ancestors req.action).isSome = true`. This is the same guard
 `isAuthorizedPartialWithSlicedPolicies` checks before slicing.

 The guard is necessary: without it the statement is false. See
 `DroppedPolicy.Counterexample.not_without_ancestors` at the end of this file
 (`action in Action::"b"` for request action `Action::"a"` with an empty entity
 store evaluates to the residual `Action::"a" in Action::"b"`, not `false`).

 Proof structure (no brute-force unfolding of the whole policy):
 * `G x`: every typing of `x` evaluates to an error-free residual, and a
   `.bool .ff` typing evaluates to literal `false`.
 * `F x`: every typing of `x` is `.bool .ff` and evaluates to literal `false`.
 * `F_and_left`, `F_and_right`, `G_and`: how `G`/`F` propagate through `&&`.
 * `scope_var`: principal/resource scopes satisfy `G`, and `F` when
   `Scope.mayMatchType` is `false`.
 * `act_scope`: substituted action scopes satisfy `G`, and `F` when
   `ActionScope.sliceForAction` is `none`.
-/
import Cedar.Thm.TPE.SlicedPoliciesActionInAny

namespace Cedar.Thm.SlicedPoliciesDropped

open Cedar.Data Cedar.Spec Cedar.Validation Cedar.TPE
open Cedar.Thm.SlicedPoliciesActionInAny

def IsFalse (r : Residual) : Prop := ∃ ty, r = .val (.prim (.bool false)) ty

theorem isFalse_errorFree {r : Residual} (h : IsFalse r) : r.errorFree = true := by
  obtain ⟨ty, rfl⟩ := h; simp [Residual.errorFree]

theorem and_val_false {l : Residual} (rty ty : CedarType) (hl : l.errorFree = true) :
    IsFalse (Cedar.TPE.and l (.val (.prim (.bool false)) rty) ty) := by
  unfold Cedar.TPE.and
  split <;> simp_all [IsFalse, Residual.errorFree]

theorem and_errorFree {l r : Residual} (ty : CedarType)
    (hl : l.errorFree = true) (hr : r.errorFree = true) :
    (Cedar.TPE.and l r ty).errorFree = true := by
  unfold Cedar.TPE.and
  split <;> simp_all [Residual.errorFree]


def G (env : TypeEnv) (req : PartialRequest) (es : PartialEntities) (x : Expr) : Prop :=
  ∀ c tx cx, typeOf x c env = .ok (tx, cx) →
    (ev env req es tx).errorFree = true ∧ (tx.typeOf = .bool .ff → IsFalse (ev env req es tx))

def F (env : TypeEnv) (req : PartialRequest) (es : PartialEntities) (x : Expr) : Prop :=
  ∀ c tx cx, typeOf x c env = .ok (tx, cx) →
    tx.typeOf = .bool .ff ∧ IsFalse (ev env req es tx)

theorem F_G {env req es x} (h : F env req es x) : G env req es x := by
  intro c tx cx ht
  obtain ⟨h1, h2⟩ := h c tx cx ht
  exact ⟨isFalse_errorFree h2, fun _ => h2⟩

/-- Shape of a successful `typeOfAnd`. -/
theorem typeOfAnd_ok {t₁ : TypedExpr} {c₁ : Capabilities} {r₂ : ResultType}
    {t : TypedExpr} {c : Capabilities} (h : typeOfAnd (t₁, c₁) r₂ = .ok (t, c)) :
    (t₁.typeOf = .bool .ff ∧ t = t₁) ∨
    (∃ b t₂ c₂ bt, t₁.typeOf = .bool b ∧ b ≠ .ff ∧ r₂ = .ok (t₂, c₂) ∧
      t = .and t₁ t₂ (.bool bt) ∧ (bt = .ff → t₂.typeOf = .bool .ff) ∧
      (t₂.typeOf = .bool .ff → bt = .ff)) := by
  unfold typeOfAnd at h
  simp only at h
  split at h
  · rename_i hty
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact .inl ⟨hty, h.1.symm⟩
  · rename_i b hb hty
    right
    cases hr : r₂ with
    | error e => simp [hr, bind, Except.bind] at h
    | ok r =>
      obtain ⟨t₂, c₂⟩ := r
      simp only [hr, bind, Except.bind] at h
      split at h <;> rename_i hty₂ <;>
        simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      · exact ⟨b, t₂, c₂, .ff, hty, hb, rfl, h.1.symm, fun _ => hty₂, fun _ => rfl⟩
      · exact ⟨b, t₂, c₂, b, hty, hb, rfl, h.1.symm, fun h' => absurd h' hb,
          fun h' => by rw [hty₂] at h'; cases h'⟩
      · rename_i bt₂ hnf hnt
        refine ⟨b, t₂, c₂, .anyBool, hty, hb, rfl, h.1.symm, fun h' => (by cases h'), ?_⟩
        intro h'; rw [hty₂] at h'; cases h'; exact absurd rfl hnf
  · simp [err] at h

theorem typeOf_and_ok {x y : Expr} {c : Capabilities} {env : TypeEnv} {t : TypedExpr}
    {c' : Capabilities} (h : typeOf (.and x y) c env = .ok (t, c')) :
    ∃ t₁ c₁, typeOf x c env = .ok (t₁, c₁) ∧
      ((t₁.typeOf = .bool .ff ∧ t = t₁) ∨
      (∃ b t₂ c₂ bt, t₁.typeOf = .bool b ∧ b ≠ .ff ∧ typeOf y (c ∪ c₁) env = .ok (t₂, c₂) ∧
        t = .and t₁ t₂ (.bool bt) ∧ (bt = .ff → t₂.typeOf = .bool .ff) ∧
        (t₂.typeOf = .bool .ff → bt = .ff))) := by
  rw [typeOf_and'] at h
  cases h₁ : typeOf x c env with
  | error e => simp [h₁, bind, Except.bind] at h
  | ok r =>
    obtain ⟨t₁, c₁⟩ := r
    simp only [h₁, bind, Except.bind] at h
    exact ⟨t₁, c₁, rfl, typeOfAnd_ok h⟩

theorem F_and_left {env req es x y} (hx : F env req es x) : F env req es (.and x y) := by
  intro c t c' h
  obtain ⟨t₁, c₁, h₁, hcase⟩ := typeOf_and_ok h
  obtain ⟨hff, hfalse⟩ := hx c t₁ c₁ h₁
  rcases hcase with ⟨_, rfl⟩ | ⟨b, _, _, _, hb, hne, _⟩
  · exact ⟨hff, hfalse⟩
  · rw [hff] at hb; cases hb; exact absurd rfl hne

theorem F_and_right {env req es x y} (hx : G env req es x) (hy : F env req es y) :
    F env req es (.and x y) := by
  intro c t c' h
  obtain ⟨t₁, c₁, h₁, hcase⟩ := typeOf_and_ok h
  obtain ⟨hef, hff⟩ := hx c t₁ c₁ h₁
  rcases hcase with ⟨hty, rfl⟩ | ⟨b, t₂, c₂, bt, _, _, h₂, rfl, _, hbt⟩
  · exact ⟨hty, hff hty⟩
  · obtain ⟨hty₂, ty₂, hev₂⟩ := hy _ t₂ c₂ h₂
    refine ⟨by rw [hbt hty₂]; rfl, ?_⟩
    rw [ev_and, hev₂]
    exact and_val_false _ _ hef

theorem G_and {env req es x y} (hx : G env req es x) (hy : G env req es y) :
    G env req es (.and x y) := by
  intro c t c' h
  obtain ⟨t₁, c₁, h₁, hcase⟩ := typeOf_and_ok h
  obtain ⟨hef, hff⟩ := hx c t₁ c₁ h₁
  rcases hcase with ⟨_, rfl⟩ | ⟨b, t₂, c₂, bt, _, _, h₂, rfl, hbt, _⟩
  · exact ⟨hef, hff⟩
  · obtain ⟨hef₂, hff₂⟩ := hy _ t₂ c₂ h₂
    refine ⟨by rw [ev_and]; exact and_errorFree _ hef hef₂, ?_⟩
    intro hty
    have hbt' : bt = .ff := by simpa [TypedExpr.typeOf] using hty
    obtain ⟨ty₂, hev₂⟩ := hff₂ (hbt hbt')
    rw [ev_and, hev₂]
    exact and_val_false _ _ hef


/-! ### Principal and resource scopes -/

section VarScope

variable {env : TypeEnv} {req : PartialRequest} {es : PartialEntities} {v : Var} {e : EntityType}

def VarShape (env : TypeEnv) (req : PartialRequest) (v : Var) (e : EntityType) : Prop :=
  typeOfVar v env = .ok (.var v (.entity e), ∅) ∧
  (varₚ req v (.entity e) = .var v (.entity e) ∨
    ∃ u, varₚ req v (.entity e) = .val (.prim (.entityUID u)) (.entity e))

theorem ev_var : ev env req es (.var v (.entity e)) = varₚ req v (.entity e) := by
  simp only [ev, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, TypedExpr.toResidual]
  rw [Cedar.TPE.evaluate]

theorem typeOf_var_lit {op : BinaryOp} {uid : EntityUID} {c cx : Capabilities} {tx : TypedExpr}
    (hv : VarShape env req v e)
    (h : typeOf (.binaryApp op (.var v) (.lit (.entityUID uid))) c env = .ok (tx, cx)) :
    typeOfBinaryApp op (.var v (.entity e)) (.lit (.entityUID uid) (.entity uid.ty))
      (.var v) (.lit (.entityUID uid)) c env = .ok (tx, cx) := by
  simp only [typeOf] at h
  rw [hv.1] at h
  simp only [typeOfLit, bind, Except.bind] at h
  by_cases hvalid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true
  · simpa [hvalid, ok] using h
  · simp [hvalid, err] at h


theorem ev_var_lit {op : BinaryOp} {uid : EntityUID} {ty : CedarType} :
    ev env req es (.binaryApp op (.var v (.entity e)) (.lit (.entityUID uid) (.entity uid.ty)) ty) =
      apply₂ env op (varₚ req v (.entity e)) (.val (.prim (.entityUID uid)) (.entity uid.ty)) es
        ty.liftBoolTypes := by
  simp only [ev, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, TypedExpr.toResidual]
  rw [Cedar.TPE.evaluate, Cedar.TPE.evaluate, Cedar.TPE.evaluate]

theorem apply₂_eq_var (hv : VarShape env req v e) (uid : EntityUID) (ty : CedarType) :
    (apply₂ env .eq (varₚ req v (.entity e)) (.val (.prim (.entityUID uid)) (.entity uid.ty)) es ty).errorFree = true ∧
    (e ≠ uid.ty → IsFalse (apply₂ env .eq (varₚ req v (.entity e))
      (.val (.prim (.entityUID uid)) (.entity uid.ty)) es ty)) := by
  rcases hv.2 with hr | ⟨u, hr⟩ <;> rw [hr] <;>
    by_cases he : e = uid.ty <;>
    simp [Cedar.TPE.apply₂, tryDecideResidual₂, Residual.errorFree, Residual.typeOf, Residual.asValue,
      IsFalse, he, BinaryOp.canError, Cedar.TPE.apply₂.self]


theorem apply₂_mem_var (hv : VarShape env req v e) (uid : EntityUID) (ty : CedarType) :
    (Cedar.TPE.apply₂ env .mem (varₚ req v (.entity e)) (.val (.prim (.entityUID uid)) (.entity uid.ty)) es ty).errorFree = true ∧
    (env.descendentOf e uid.ty = false → IsFalse (Cedar.TPE.apply₂ env .mem (varₚ req v (.entity e))
      (.val (.prim (.entityUID uid)) (.entity uid.ty)) es ty)) := by
  rcases hv.2 with hr | ⟨u, hr⟩ <;> rw [hr] <;>
    cases hd : env.descendentOf e uid.ty <;>
    simp [Cedar.TPE.apply₂, tryDecideResidual₂, Residual.errorFree, Residual.typeOf, Residual.asValue,
      IsFalse, hd, BinaryOp.canError, Cedar.TPE.apply₂.self, someOrSelf]
  -- Remaining goal: a concrete principal/resource `in` an entity of a reachable type.
  split <;> simp [Residual.errorFree, BinaryOp.canError]

theorem apply₁_is_var (hv : VarShape env req v e) (ety : EntityType) (ty : CedarType) :
    (Cedar.TPE.apply₁ (.is ety) (varₚ req v (.entity e)) ty).errorFree = true ∧
    (ety ≠ e → IsFalse (Cedar.TPE.apply₁ (.is ety) (varₚ req v (.entity e)) ty)) := by
  rcases hv.2 with hr | ⟨u, hr⟩ <;> rw [hr] <;>
    by_cases he : ety = e <;>
    simp [Cedar.TPE.apply₁, tryDecideResidual₁, Residual.errorFree, Residual.typeOf, IsFalse, he]

theorem typeOf_eq_var (hv : VarShape env req v e) {uid : EntityUID} {c cx : Capabilities} {tx : TypedExpr}
    (h : typeOf (v.eqEntityUID uid) c env = .ok (tx, cx)) :
    tx = .binaryApp .eq (.var v (.entity e)) (.lit (.entityUID uid) (.entity uid.ty))
      (.bool (if e = uid.ty then .anyBool else .ff)) := by
  have h' := typeOf_var_lit hv h
  by_cases he : e = uid.ty <;>
    simp [typeOfBinaryApp, typeOfEq, TypedExpr.typeOf, lub?, ok, he] at h' <;>
    simp [he, h'.1]

theorem typeOf_mem_var (hv : VarShape env req v e) {uid : EntityUID} {c cx : Capabilities} {tx : TypedExpr}
    (h : typeOf (v.inEntityUID uid) c env = .ok (tx, cx)) :
    tx = .binaryApp .mem (.var v (.entity e)) (.lit (.entityUID uid) (.entity uid.ty))
      (.bool (if env.descendentOf e uid.ty then .anyBool else .ff)) := by
  have h' := typeOf_var_lit hv h
  simp [typeOfBinaryApp, typeOfInₑ, TypedExpr.typeOf, actionUID?, entityUID?, ok] at h'
  exact h'.1.symm

theorem typeOf_is_var (hv : VarShape env req v e) {ety : EntityType} {c cx : Capabilities} {tx : TypedExpr}
    (h : typeOf (v.isEntityType ety) c env = .ok (tx, cx)) :
    tx = .unaryApp (.is ety) (.var v (.entity e)) (.bool (if ety = e then .tt else .ff)) := by
  simp only [Var.isEntityType, typeOf] at h
  rw [hv.1] at h
  simp [bind, Except.bind, typeOfUnaryApp, TypedExpr.typeOf, ok] at h
  exact h.1.symm


theorem G_true : G env req es (.lit (.bool true)) := by
  intro c tx cx h
  simp [typeOf, typeOfLit, ok] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, fun h => by simp [TypedExpr.typeOf] at h⟩
  simp only [ev, TypedExpr.liftBoolTypes, TypedExpr.toResidual]
  rw [Cedar.TPE.evaluate]; simp [Residual.errorFree]

theorem scope_eq (hv : VarShape env req v e) (uid : EntityUID) :
    G env req es (v.eqEntityUID uid) ∧ (e ≠ uid.ty → F env req es (v.eqEntityUID uid)) := by
  constructor
  · intro c tx cx h
    rw [typeOf_eq_var hv h, ev_var_lit]
    obtain ⟨h1, h2⟩ := apply₂_eq_var (es := es) hv uid
      (CedarType.bool (if e = uid.ty then .anyBool else .ff)).liftBoolTypes
    refine ⟨h1, fun hff => h2 ?_⟩
    intro he; simp [TypedExpr.typeOf, he] at hff
  · intro hne c tx cx h
    rw [typeOf_eq_var hv h, ev_var_lit]
    exact ⟨by simp [TypedExpr.typeOf, hne], (apply₂_eq_var hv uid _).2 hne⟩

theorem scope_mem (hv : VarShape env req v e) (uid : EntityUID) :
    G env req es (v.inEntityUID uid) ∧
      (env.descendentOf e uid.ty = false → F env req es (v.inEntityUID uid)) := by
  constructor
  · intro c tx cx h
    rw [typeOf_mem_var hv h, ev_var_lit]
    obtain ⟨h1, h2⟩ := apply₂_mem_var (es := es) hv uid
      (CedarType.bool (if env.descendentOf e uid.ty then .anyBool else .ff)).liftBoolTypes
    refine ⟨h1, fun hff => h2 ?_⟩
    cases hd : env.descendentOf e uid.ty
    · rfl
    · simp [TypedExpr.typeOf, hd] at hff
  · intro hne c tx cx h
    rw [typeOf_mem_var hv h, ev_var_lit]
    exact ⟨by simp [TypedExpr.typeOf, hne], (apply₂_mem_var hv uid _).2 hne⟩

theorem ev_is_var {ety : EntityType} {ty : CedarType} :
    ev env req es (.unaryApp (.is ety) (.var v (.entity e)) ty) =
      Cedar.TPE.apply₁ (.is ety) (varₚ req v (.entity e)) ty.liftBoolTypes := by
  simp only [ev, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, TypedExpr.toResidual]
  rw [Cedar.TPE.evaluate, Cedar.TPE.evaluate]

theorem scope_is (hv : VarShape env req v e) (ety : EntityType) :
    G env req es (v.isEntityType ety) ∧ (ety ≠ e → F env req es (v.isEntityType ety)) := by
  constructor
  · intro c tx cx h
    rw [typeOf_is_var hv h, ev_is_var]
    obtain ⟨h1, h2⟩ := apply₁_is_var hv ety
      (CedarType.bool (if ety = e then .tt else .ff)).liftBoolTypes
    refine ⟨h1, fun hff => h2 ?_⟩
    intro he; simp [TypedExpr.typeOf, he] at hff
  · intro hne c tx cx h
    rw [typeOf_is_var hv h, ev_is_var]
    exact ⟨by simp [TypedExpr.typeOf, hne], (apply₁_is_var hv ety _).2 hne⟩

/-- Every principal/resource scope is error-free and type-sound; an impossible
    scope (per `Scope.mayMatchType`) always evaluates to literal `false`. -/
theorem scope_var (hv : VarShape env req v e) (s : Scope) :
    G env req es (s.toExpr v) ∧
      (Cedar.TPE.Scope.mayMatchType s e env = false → F env req es (s.toExpr v)) := by
  cases s with
  | any => exact ⟨G_true, fun h => by simp [Cedar.TPE.Scope.mayMatchType] at h⟩
  | eq uid =>
    obtain ⟨hg, hf⟩ := scope_eq (es := es) hv uid
    exact ⟨hg, fun h => hf (by simpa [Cedar.TPE.Scope.mayMatchType] using h)⟩
  | mem uid =>
    obtain ⟨hg, hf⟩ := scope_mem (es := es) hv uid
    exact ⟨hg, fun h => hf (by simpa [Cedar.TPE.Scope.mayMatchType] using h)⟩
  | is ety =>
    obtain ⟨hg, hf⟩ := scope_is (es := es) hv ety
    exact ⟨hg, fun h => hf (fun he => by subst he; simp [Cedar.TPE.Scope.mayMatchType] at h)⟩
  | isMem ety uid =>
    obtain ⟨hgi, hfi⟩ := scope_is (es := es) hv ety
    obtain ⟨hgm, hfm⟩ := scope_mem (es := es) hv uid
    refine ⟨G_and hgi hgm, fun h => ?_⟩
    simp only [Scope.toExpr]
    by_cases he : ety = e
    · subst he
      exact F_and_right hgi (hfm (by simpa [Cedar.TPE.Scope.mayMatchType] using h))
    · exact F_and_left (hfi he)

end VarScope

/-! ### Action scopes (action substituted by a concrete literal) -/

section ActScope

variable {env : TypeEnv} {req : PartialRequest} {es : PartialEntities} {a : EntityUID}

theorem subst_scope_action (a : EntityUID) (s : Scope) :
    substituteAction a (s.toExpr .action) =
      match s with
      | .any => .lit (.bool true)
      | .eq uid => .binaryApp .eq (.lit (.entityUID a)) (.lit (.entityUID uid))
      | .mem uid => .binaryApp .mem (.lit (.entityUID a)) (.lit (.entityUID uid))
      | .is ety => .unaryApp (.is ety) (.lit (.entityUID a))
      | .isMem ety uid => .and (.unaryApp (.is ety) (.lit (.entityUID a)))
          (.binaryApp .mem (.lit (.entityUID a)) (.lit (.entityUID uid))) := by
  cases s <;> simp [substituteAction, mapOnVars, Scope.toExpr, Var.eqEntityUID, Var.inEntityUID,
    Var.isEntityType]

theorem typeOf_lit_act (hcont : env.acts.contains a = true) (c : Capabilities) :
    typeOf (.lit (.entityUID a)) c env = .ok (.lit (.entityUID a) (.entity a.ty), ∅) := by
  simp [typeOf, typeOfLit, hcont, ok]

theorem typeOf_lit_lit {op : BinaryOp} {uid : EntityUID} {c cx : Capabilities} {tx : TypedExpr}
    (hcont : env.acts.contains a = true)
    (h : typeOf (.binaryApp op (.lit (.entityUID a)) (.lit (.entityUID uid))) c env = .ok (tx, cx)) :
    typeOfBinaryApp op (.lit (.entityUID a) (.entity a.ty)) (.lit (.entityUID uid) (.entity uid.ty))
      (.lit (.entityUID a)) (.lit (.entityUID uid)) c env = .ok (tx, cx) := by
  rw [typeOf, typeOf_lit_act hcont] at h
  simp only [typeOf, typeOfLit, bind, Except.bind] at h
  by_cases hvalid : (env.ets.isValidEntityUID uid || env.acts.contains uid) = true
  · simpa [hvalid, ok] using h
  · simp [hvalid, err] at h

theorem ev_lit_lit {op : BinaryOp} {uid : EntityUID} {ty : CedarType} :
    ev env req es (.binaryApp op (.lit (.entityUID a) (.entity a.ty)) (.lit (.entityUID uid) (.entity uid.ty)) ty) =
      Cedar.TPE.apply₂ env op (.val (.prim (.entityUID a)) (.entity a.ty))
        (.val (.prim (.entityUID uid)) (.entity uid.ty)) es ty.liftBoolTypes := by
  simp only [ev, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, TypedExpr.toResidual]
  rw [Cedar.TPE.evaluate, Cedar.TPE.evaluate, Cedar.TPE.evaluate]

theorem act_eq (hcont : env.acts.contains a = true) (uid : EntityUID) :
    G env req es (.binaryApp .eq (.lit (.entityUID a)) (.lit (.entityUID uid))) ∧
      (a ≠ uid → F env req es (.binaryApp .eq (.lit (.entityUID a)) (.lit (.entityUID uid)))) := by
  have key : ∀ c tx cx, typeOf (.binaryApp .eq (.lit (.entityUID a)) (.lit (.entityUID uid))) c env = .ok (tx, cx) →
      tx.typeOf = .bool (if a = uid then .tt else .ff) ∧
      (ev env req es tx).errorFree = true ∧ (a ≠ uid → IsFalse (ev env req es tx)) := by
    intro c tx cx h
    have h' := typeOf_lit_lit hcont h
    simp only [typeOfBinaryApp, typeOfEq] at h'
    by_cases hau : a = uid
    · subst hau
      simp [ok] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [ev_lit_lit]
      simp [TypedExpr.typeOf, Cedar.TPE.apply₂, tryDecideResidual₂, Residual.errorFree,
        Residual.typeOf, Residual.asValue]
    · have hp : (Prim.entityUID a == Prim.entityUID uid) = false := by simp [hau]
      simp [hp, ok] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [ev_lit_lit]
      by_cases ht : a.ty = uid.ty <;>
        simp [TypedExpr.typeOf, Cedar.TPE.apply₂, tryDecideResidual₂, Residual.errorFree,
          Residual.typeOf, Residual.asValue, hau, ht, IsFalse]
  constructor
  · intro c tx cx h
    obtain ⟨h1, h2, h3⟩ := key c tx cx h
    refine ⟨h2, fun hff => h3 ?_⟩
    intro hau; subst hau; simp [h1] at hff
  · intro hau c tx cx h
    obtain ⟨h1, _, h3⟩ := key c tx cx h
    exact ⟨by simp [h1, hau], h3 hau⟩

theorem act_mem (hcont : env.acts.contains a = true)
    (hin : ∀ u, Cedar.TPE.inₑ a u es = some (env.acts.descendentOf a u)) (uid : EntityUID) :
    G env req es (.binaryApp .mem (.lit (.entityUID a)) (.lit (.entityUID uid))) ∧
      (env.acts.descendentOf a uid = false →
        F env req es (.binaryApp .mem (.lit (.entityUID a)) (.lit (.entityUID uid)))) := by
  have key : ∀ c tx cx, typeOf (.binaryApp .mem (.lit (.entityUID a)) (.lit (.entityUID uid))) c env = .ok (tx, cx) →
      tx.typeOf = .bool (if env.acts.descendentOf a uid then .tt else .ff) ∧
      (ev env req es tx).errorFree = true ∧
      (env.acts.descendentOf a uid = false → IsFalse (ev env req es tx)) := by
    intro c tx cx h
    have h' := typeOf_lit_lit hcont h
    simp [typeOfBinaryApp, typeOfInₑ, TypedExpr.typeOf, actionUID?, entityUID?, hcont, ok] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rw [ev_lit_lit]
    cases hd : env.acts.descendentOf a uid <;> cases hd' : env.descendentOf a.ty uid.ty <;>
      simp [TypedExpr.typeOf, Cedar.TPE.apply₂, tryDecideResidual₂, Residual.errorFree,
        Residual.typeOf, Residual.asValue, hd, hd', IsFalse, someOrSelf, hin]
  constructor
  · intro c tx cx h
    obtain ⟨h1, h2, h3⟩ := key c tx cx h
    refine ⟨h2, fun hff => h3 ?_⟩
    cases hd : env.acts.descendentOf a uid
    · rfl
    · simp [h1, hd] at hff
  · intro hd c tx cx h
    obtain ⟨h1, _, h3⟩ := key c tx cx h
    exact ⟨by simp [h1, hd], h3 hd⟩

theorem act_is (hcont : env.acts.contains a = true) (ety : EntityType) :
    G env req es (.unaryApp (.is ety) (.lit (.entityUID a))) ∧
      (ety ≠ a.ty → F env req es (.unaryApp (.is ety) (.lit (.entityUID a)))) := by
  have key : ∀ c tx cx, typeOf (.unaryApp (.is ety) (.lit (.entityUID a))) c env = .ok (tx, cx) →
      tx.typeOf = .bool (if ety = a.ty then .tt else .ff) ∧
      (ev env req es tx).errorFree = true ∧ (ety ≠ a.ty → IsFalse (ev env req es tx)) := by
    intro c tx cx h
    rw [typeOf, typeOf_lit_act hcont] at h
    simp [bind, Except.bind, typeOfUnaryApp, TypedExpr.typeOf, ok] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [ev, TypedExpr.liftBoolTypes, CedarType.liftBoolTypes, TypedExpr.toResidual]
    rw [Cedar.TPE.evaluate, Cedar.TPE.evaluate]
    by_cases he : ety = a.ty <;>
      simp [TypedExpr.typeOf, Cedar.TPE.apply₁, tryDecideResidual₁, Residual.errorFree,
        Residual.typeOf, he, IsFalse]
  constructor
  · intro c tx cx h
    obtain ⟨h1, h2, h3⟩ := key c tx cx h
    refine ⟨h2, fun hff => h3 ?_⟩
    intro he; simp [h1, he] at hff
  · intro he c tx cx h
    obtain ⟨h1, _, h3⟩ := key c tx cx h
    exact ⟨by simp [h1, he], h3 he⟩

theorem mapM_asEntityUID_sub (ws : List Value)
    (h : ∀ w ∈ ws, ∃ u, w = Value.prim (Prim.entityUID u)) :
    ∃ L, ws.mapM (Except.toOption ∘ Value.asEntityUID) = some L ∧
      ∀ u ∈ L, Value.prim (Prim.entityUID u) ∈ ws := by
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
      rcases hv with rfl | hv
      · simp
      · exact List.mem_cons_of_mem _ (hmem v hv)

theorem inₛ_make_false (us : List EntityUID)
    (h : ∀ u ∈ us, Cedar.TPE.inₑ a u es = some false) :
    inₛ a (Set.make (us.map fun x => Value.prim (Prim.entityUID x))) es = some false := by
  obtain ⟨L, hL, hmem⟩ := mapM_asEntityUID_sub
    (Set.make (us.map fun x => Value.prim (Prim.entityUID x))).toList (by
      intro w hw
      have : w ∈ Set.make (us.map fun x => Value.prim (Prim.entityUID x)) := hw
      rw [Set.mem_make] at this
      simp only [List.mem_map] at this
      obtain ⟨u, _, rfl⟩ := this
      exact ⟨u, rfl⟩)
  have hL' : ∀ u ∈ L, Cedar.TPE.inₑ a u es = some false := by
    intro u hu
    have : Value.prim (Prim.entityUID u) ∈ Set.make (us.map fun x => Value.prim (Prim.entityUID x)) :=
      hmem u hu
    rw [Set.mem_make] at this
    simp only [List.mem_map] at this
    obtain ⟨u', hu', heq⟩ := this
    simp only [Value.prim.injEq, Prim.entityUID.injEq] at heq
    rw [← heq]
    exact h u' hu'
  simp only [Cedar.TPE.inₛ, hL, bind, Option.bind, List.ternaryAny]
  have h1 : (L.map (Cedar.TPE.inₑ a · es)).any (· == some true) = false := by
    simp only [List.any_eq_false, List.mem_map]
    rintro _ ⟨u, hu, rfl⟩
    simp [hL' u hu]
  have h2 : (L.map (Cedar.TPE.inₑ a · es)).any Option.isNone = false := by
    simp only [List.any_eq_false, List.mem_map]
    rintro _ ⟨u, hu, rfl⟩
    simp [hL' u hu]
  simp [h1, h2]

theorem apply₂_mem_set (S : Set Value) (e : EntityType) (ty : CedarType) (b : Bool)
    (h : inₛ a S es = some b) :
    Cedar.TPE.apply₂ env .mem (.val (.prim (.entityUID a)) (.entity a.ty)) (.val (.set S) (.set (.entity e))) es ty =
      .val (if env.descendentOf a.ty e then b else false) ty := by
  simp [Cedar.TPE.apply₂, tryDecideResidual₂, Residual.errorFree, Residual.typeOf, Residual.asValue,
    someOrSelf, h]
  cases env.descendentOf a.ty e <;> rfl

theorem eval_actTyped_b (us : List EntityUID) (e : EntityType) (bt : BoolType) (b : Bool)
    (h : inₛ a (Set.make (us.map fun x => Value.prim (Prim.entityUID x))) es = some b) :
    ev env req es (actTyped a us e bt) =
      .val (if env.descendentOf a.ty e then b else false) (.bool bt.lift) := by
  simp [ev, actTyped, TypedExpr.liftBoolTypes, TypedExpr.toResidual, CedarType.liftBoolTypes, Cedar.TPE.evaluate,
    List.map₁_eq_map, typedLits, List.map_map, Function.comp_def, Cedar.TPE.set]
  rw [List.map₁_eq_map (fun x => Cedar.TPE.evaluate env x req es)]
  simp only [List.map_map, Function.comp_def, Cedar.TPE.evaluate]
  rw [mapM_asValue_vals]
  exact apply₂_mem_set _ e _ b h

theorem act_any (hcont : env.acts.contains a = true)
    (hin : ∀ u, Cedar.TPE.inₑ a u es = some (env.acts.descendentOf a u)) (us : List EntityUID) :
    G env req es (actExpr a us) ∧
      (us.any (env.acts.descendentOf a ·) = false → F env req es (actExpr a us)) := by
  have key : ∀ c tx cx, typeOf (actExpr a us) c env = .ok (tx, cx) →
      tx.typeOf = .bool (if us.any (env.acts.descendentOf a ·) then .tt else .ff) ∧
      (ev env req es tx).errorFree = true ∧
      (us.any (env.acts.descendentOf a ·) = false → IsFalse (ev env req es tx)) := by
    intro c tx cx h
    obtain ⟨e, _, _, _, rfl⟩ := typeOf_actExpr hcont h
    cases hany : us.any (env.acts.descendentOf a ·)
    · have hf : inₛ a (Set.make (us.map fun x => Value.prim (Prim.entityUID x))) es = some false := by
        apply inₛ_make_false
        intro u hu
        rw [hin u]
        have := List.any_eq_false.mp hany u hu
        simpa using this
      rw [eval_actTyped_b _ _ _ _ hf]
      refine ⟨rfl, by simp [Residual.errorFree], fun _ => ?_⟩
      simp [IsFalse]
    · obtain ⟨k, hk, hdk⟩ := List.any_eq_true.mp hany
      have ht := inₛ_make_true a us es ⟨k, hk, by rw [hin k]; simpa using hdk⟩
      rw [eval_actTyped_b _ _ _ _ ht]
      exact ⟨rfl, by simp [Residual.errorFree], fun h => by cases h⟩
  constructor
  · intro c tx cx h
    obtain ⟨h1, h2, h3⟩ := key c tx cx h
    refine ⟨h2, fun hff => h3 ?_⟩
    cases hd : us.any (env.acts.descendentOf a ·)
    · rfl
    · simp [h1, hd] at hff
  · intro hd c tx cx h
    obtain ⟨h1, _, h3⟩ := key c tx cx h
    exact ⟨by simp [h1, hd], h3 hd⟩

/-- Every substituted action scope is error-free and type-sound; an action
    scope that `ActionScope.sliceForAction` drops evaluates to literal `false`. -/
theorem act_scope (hcont : env.acts.contains a = true)
    (hin : ∀ u, Cedar.TPE.inₑ a u es = some (env.acts.descendentOf a u)) (asc : ActionScope) :
    G env req es (substituteAction a asc.toExpr) ∧
      (Cedar.TPE.ActionScope.sliceForAction asc a env.acts = none →
        F env req es (substituteAction a asc.toExpr)) := by
  cases asc with
  | actionScope s =>
    simp only [ActionScope.toExpr]
    rw [subst_scope_action]
    cases s with
    | any => exact ⟨G_true, fun h => by simp [Cedar.TPE.ActionScope.sliceForAction] at h⟩
    | eq uid =>
      obtain ⟨hg, hf⟩ := act_eq (req := req) (es := es) hcont uid
      exact ⟨hg, fun h => hf (by simpa [Cedar.TPE.ActionScope.sliceForAction] using h)⟩
    | mem uid =>
      obtain ⟨hg, hf⟩ := act_mem (req := req) hcont hin uid
      exact ⟨hg, fun h => hf (by simpa [Cedar.TPE.ActionScope.sliceForAction] using h)⟩
    | is ety =>
      obtain ⟨hg, hf⟩ := act_is (req := req) (es := es) hcont ety
      exact ⟨hg, fun h => hf (fun he => by subst he; simp [Cedar.TPE.ActionScope.sliceForAction] at h)⟩
    | isMem ety uid =>
      obtain ⟨hgi, hfi⟩ := act_is (req := req) (es := es) hcont ety
      obtain ⟨hgm, hfm⟩ := act_mem (req := req) hcont hin uid
      refine ⟨G_and hgi hgm, fun h => ?_⟩
      by_cases he : ety = a.ty
      · subst he
        exact F_and_right hgi (hfm (by simpa [Cedar.TPE.ActionScope.sliceForAction] using h))
      · exact F_and_left (hfi he)
  | actionInAny us =>
    rw [subst_actionInAny]
    obtain ⟨hg, hf⟩ := act_any (req := req) hcont hin us
    refine ⟨hg, fun h => hf ?_⟩
    simp only [Cedar.TPE.ActionScope.sliceForAction] at h
    split at h
    · rename_i hemp
      rw [List.isEmpty_iff, List.filter_eq_nil_iff] at hemp
      exact List.any_eq_false.mpr (fun u hu => by simpa using hemp u hu)
    · cases h

end ActScope

/-! ### Assembly -/

theorem subst_scope_nonaction (a : EntityUID) (s : Scope) (v : Var) (hv : v ≠ .action) :
    substituteAction a (s.toExpr v) = s.toExpr v := by
  cases v
  case action => exact absurd rfl hv
  all_goals
    cases s <;> simp [substituteAction, mapOnVars, Scope.toExpr, Var.eqEntityUID,
      Var.inEntityUID, Var.isEntityType]

theorem varShape_principal (env : TypeEnv) (req : PartialRequest) :
    VarShape env req .principal env.reqty.principal := by
  refine ⟨rfl, ?_⟩
  simp only [varₚ, varₚ.varₒ, someOrSelf]
  cases req.principal.asEntityUID <;> simp

theorem varShape_resource (env : TypeEnv) (req : PartialRequest) :
    VarShape env req .resource env.reqty.resource := by
  refine ⟨rfl, ?_⟩
  simp only [varₚ, varₚ.varₒ, someOrSelf]
  cases req.resource.asEntityUID <;> simp

/-- A dropped policy fails exactly one of the three slicing checks. -/
theorem slice_none_cases {p : Policy} {env : TypeEnv}
    (h : Cedar.TPE.Policy.sliceForRequestEnv p env = none) :
    Cedar.TPE.Scope.mayMatchType p.principalScope.scope env.reqty.principal env = false ∨
    Cedar.TPE.ActionScope.sliceForAction p.actionScope env.reqty.action env.acts = none ∨
    Cedar.TPE.Scope.mayMatchType p.resourceScope.scope env.reqty.resource env = false := by
  unfold Cedar.TPE.Policy.sliceForRequestEnv at h
  cases hP : Cedar.TPE.Scope.mayMatchType p.principalScope.scope env.reqty.principal env
  · exact .inl rfl
  cases hA : Cedar.TPE.ActionScope.sliceForAction p.actionScope env.reqty.action env.acts
  · exact .inr (.inl rfl)
  cases hR : Cedar.TPE.Scope.mayMatchType p.resourceScope.scope env.reqty.resource env
  · exact .inr (.inr rfl)
  simp [hP, hA, hR, bind, Option.bind] at h

/-- Under the request-action ancestor invariant, a policy dropped by
    `Policy.sliceForRequestEnv` partially evaluates to literal `false`. -/
theorem evaluatePolicy_dropped_isFalse
    {schema : Schema} {req : PartialRequest} {env : TypeEnv} {p : Policy}
    {es : PartialEntities} {r : Residual}
    (hreq : validatePartialRequest schema req = .ok env)
    (hanc : (es.ancestors req.action).isSome = true)
    (hslice : Cedar.TPE.Policy.sliceForRequestEnv p env = none)
    (heval : evaluatePolicy schema p req es = .ok r) :
    r.isFalse = true := by
  obtain ⟨ase, hfind, hets, hacts, hact⟩ := env_facts hreq
  have hsch : env.schema = schema := by simp only [TypeEnv.schema, hets, hacts]
  unfold evaluatePolicy at heval
  rw [hreq] at heval
  simp only [hsch] at heval
  split at heval
  case isFalse => cases heval
  rename_i hes
  have hcont : env.acts.contains env.reqty.action = true := by
    rw [hacts, hact]; simp [ActionSchema.contains, hfind]
  have hin : ∀ u, Cedar.TPE.inₑ env.reqty.action u es =
      some (env.acts.descendentOf env.reqty.action u) := by
    rw [hacts, hact]
    intro u
    obtain ⟨ancs, hancs⟩ := Option.isSome_iff_exists.mp hanc
    have hA := ancestors_eq hes hfind hancs
    subst hA
    unfold Cedar.TPE.inₑ
    by_cases hau : req.action = u
    · simp [hau, ActionSchema.descendentOf]
    · simp [hau, hancs, ActionSchema.descendentOf, hfind]
  -- The substituted policy expression is literally false-typed and false-valued.
  have hF : F env req es (substituteAction env.reqty.action p.toExpr) := by
    rw [policy_toExpr_subst]
    have hP := scope_var (es := es) (varShape_principal env req) p.principalScope.scope
    have hR := scope_var (es := es) (varShape_resource env req) p.resourceScope.scope
    have hA := act_scope (req := req) hcont hin p.actionScope
    have hpe : substituteAction env.reqty.action p.principalScope.toExpr =
        p.principalScope.scope.toExpr .principal := by
      cases p.principalScope
      exact subst_scope_nonaction _ _ _ (by decide)
    have hre : substituteAction env.reqty.action p.resourceScope.toExpr =
        p.resourceScope.scope.toExpr .resource := by
      cases p.resourceScope
      exact subst_scope_nonaction _ _ _ (by decide)
    rw [hpe, hre]
    rcases slice_none_cases hslice with h | h | h
    · exact F_and_left (hP.2 h)
    · exact F_and_right hP.1 (F_and_left (hA.2 h))
    · exact F_and_right hP.1 (F_and_right hA.1 (F_and_left (hR.2 h)))
  cases hc : checkEntities schema p.toExpr with
  | error e => simp [hc, Except.mapError, bind, Except.bind] at heval
  | ok u =>
    cases ht : typeOf (substituteAction env.reqty.action p.toExpr) ∅ env with
    | error e => simp only [hc, ht, Except.mapError, bind, Except.bind] at heval; cases heval
    | ok tc =>
      obtain ⟨te, cte⟩ := tc
      simp only [hc, ht, Except.mapError, bind, Except.bind, Except.ok.injEq] at heval
      subst heval
      obtain ⟨_, ty, hev⟩ := hF ∅ te cte ht
      have : Cedar.TPE.evaluate env te.liftBoolTypes.toResidual req es =
          .val (.prim (.bool false)) ty := hev
      rw [this]
      rfl


end Cedar.Thm.SlicedPoliciesDropped
