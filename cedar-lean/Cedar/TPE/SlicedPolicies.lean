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

import Cedar.TPE.Authorizer
import Cedar.Validation.Decompose

/-!
Partial authorization with policies sliced for the request environment.

The caller supplies the already-composed schema slice: the entity schema plus
only the concrete request action and its transitive action closure. This module
never inspects the full schema.

Policies whose principal, action, or resource scope cannot match the request
environment are omitted. For `action in [a₁, ..., aₙ]`, targets other than the
request action and its ancestors are removed before evaluation. This permits a
policy to mention sibling actions that are intentionally absent from the schema
slice.
-/

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- Can a scope possibly match an entity of type `actual` in `env`?

    This is deliberately based on the request environment, not on a concrete
    principal or resource id. Returning `false` means the scope is impossible;
    returning `true` does not mean it is satisfied. -/
def Scope.mayMatchType (scope : Scope) (actual : EntityType) (env : TypeEnv) : Bool :=
  match scope with
  | .any => true
  | .eq uid => actual == uid.ty
  | .mem uid => env.descendentOf actual uid.ty
  | .is ety => actual == ety
  | .isMem ety uid => actual == ety && env.descendentOf actual uid.ty

/-- Slice an action scope for the concrete request action.

    `none` means the scope cannot match and the policy can be omitted. For an
    `action in [...]` constraint, keep exactly the request action and its
    ancestors. Other action scopes are kept unchanged when they can match. -/
def ActionScope.sliceForAction
    (scope : ActionScope) (action : EntityUID) (acts : ActionSchema) : Option ActionScope :=
  match scope with
  | .actionScope .any => some scope
  | .actionScope (.eq uid) => if action == uid then some scope else none
  | .actionScope (.mem uid) => if acts.descendentOf action uid then some scope else none
  | .actionScope (.is ety) => if action.ty == ety then some scope else none
  | .actionScope (.isMem ety uid) =>
    if action.ty == ety && acts.descendentOf action uid then some scope else none
  | .actionInAny uids =>
    let kept := uids.filter (acts.descendentOf action ·)
    if kept.isEmpty then none else some (.actionInAny kept)

/-- Slice one policy for a request environment.

    Policies with an impossible principal or resource type constraint, or an
    impossible action constraint, are omitted. A retained policy differs only
    in an `action in [...]` scope, where actions outside the request action's
    closure are removed. -/
def Policy.sliceForRequestEnv (policy : Policy) (env : TypeEnv) : Option Policy := do
  if !Cedar.TPE.Scope.mayMatchType policy.principalScope.scope env.reqty.principal env then none
  let actionScope ← Cedar.TPE.ActionScope.sliceForAction policy.actionScope env.reqty.action env.acts
  if !Cedar.TPE.Scope.mayMatchType policy.resourceScope.scope env.reqty.resource env then none
  some { policy with actionScope }

/-- Slice all policies for a request environment. -/
def slicePoliciesForRequestEnv (policies : Policies) (env : TypeEnv) : Policies :=
  policies.filterMap (Cedar.TPE.Policy.sliceForRequestEnv · env)

/--
Partially authorize after slicing policies for the concrete request environment.

The supplied `schema` is expected to be the composed action slice: all entity
types plus only `req.action` and its transitive action closure. The function
never needs the full schema.

The policies and full schema must have been validated before this call. Policies
omitted by slicing are not typechecked here, so this function can succeed where
ordinary partial authorization reports an error for an invalid, inapplicable
policy. Schema slicing also requires the three executable restrictions proved
by `isAuthorizedPartialWithSlicedPolicies_refines`: no action literals or
action-type `is` tests in conditions, and no action-typed schema properties.
Those checks are performed against the full schema before it is sliced because
this function intentionally has no access to that schema.

The partial entity store may contain action entities only from the supplied
action slice. It must include `req.action` with its concrete ancestor set. An
off-slice action entity fails validation, and unknown request-action ancestors
are rejected to prevent a residual action-scope result from being mistaken for
a definite non-match.

If the partial request does not select an environment, fall back to ordinary
partial authorization on the supplied slice. Otherwise, invalid entities or
unknown request-action ancestors produce `invalidRequestOrEntities` even for an
empty policy set.
-/
def isAuthorizedPartialWithSlicedPolicies
    (schema : Schema) (policies : Policies) (req : PartialRequest)
    (entities : PartialEntities) : Except Error Response :=
  match validatePartialRequest schema req with
  | .error _ => isAuthorized schema policies req entities
  | .ok env =>
    if entitiesIsValid env.schema entities && (entities.ancestors req.action).isSome
    then isAuthorized schema (slicePoliciesForRequestEnv policies env) req entities
    else .error .invalidRequestOrEntities

end Cedar.TPE
