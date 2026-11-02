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
import Cedar.Thm.TPE.SlicedPoliciesActionInAny
import Cedar.Thm.TPE.SlicedPoliciesDropped
import Cedar.Thm.TPE.SlicedPoliciesCrossSchema

namespace Cedar.Thm

open Cedar.Spec
open Cedar.TPE
open Cedar.Validation

/-- Partial authorization using an action-sliced schema produces an equivalent
    response modulo omitted known-false policies.

    The sliced schema is required to be well formed because
    `Schema.IsActionSliceOf` constrains observable lookups but, by itself,
    permits a malformed map with shadowed duplicate keys. The request and
    partial-entity premises are the executable success-path checks performed by
    `isAuthorizedPartialWithSlicedPolicies`. -/
theorem isAuthorizedPartialWithSlicedPolicies_refines
    {fullSchema slicedSchema : Schema}
    {policies : Policies}
    {partialRequest : PartialRequest}
    {partialEntities : PartialEntities}
    {slicedRequestEnv : TypeEnv}
    {fullResponse : Cedar.TPE.Response}
    (fullSchemaWellFormed : fullSchema.validateWellFormed = .ok ())
    (slicedSchemaWellFormed : slicedSchema.validateWellFormed = .ok ())
    (schemaSlice : slicedSchema.IsActionSliceOf fullSchema partialRequest.action)
    (noActionLiteralsInConditions :
      fullSchema.noActionLiteralsInConditions policies = true)
    (noActionTypeTestsInConditions :
      fullSchema.noActionTypeTestsInConditions policies = true)
    (noActionTypedAttributes : fullSchema.noActionTypedAttrs = true)
    (slicedRequestValid :
      validatePartialRequest slicedSchema partialRequest = .ok slicedRequestEnv)
    (slicedEntityGuard :
      (entitiesIsValid slicedRequestEnv.schema partialEntities &&
        (partialEntities.ancestors partialRequest.action).isSome) = true)
    (fullAuthorization :
      TPE.isAuthorized fullSchema policies partialRequest partialEntities = .ok fullResponse) :
    ∃ slicedResponse,
      TPE.isAuthorizedPartialWithSlicedPolicies
        slicedSchema policies partialRequest partialEntities = .ok slicedResponse ∧
      slicedResponse.SliceRefines fullResponse :=
  CrossSchema.isAuthorizedPartialWithSlicedPolicies_refines_full
    fullSchemaWellFormed
    slicedSchemaWellFormed
    schemaSlice
    noActionLiteralsInConditions
    noActionTypeTestsInConditions
    noActionTypedAttributes
    slicedRequestValid
    slicedEntityGuard
    fullAuthorization

end Cedar.Thm
