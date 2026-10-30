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
import Cedar.Thm.TPE.SlicedPoliciesCrossSchema

/-!
Correctness of partial authorization with policies sliced for one request
environment.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.TPE
open Cedar.Validation

/-- Partial authorization using only an already-composed action-sliced schema
    refines partial authorization using the full schema.

    The sliced schema is required to be well formed because
    `Schema.IsActionSliceOf` constrains observable lookups but, by itself,
    permits a malformed map with shadowed duplicate keys. The request and
    partial-entity premises are the executable success-path checks performed by
    `isAuthorizedPartialWithSlicedPolicies`. -/
theorem isAuthorizedPartialWithSlicedPolicies_refines
    {full sliced : Schema} {policies : Policies} {preq : PartialRequest}
    {pes : PartialEntities} {envS : TypeEnv} {rf : Cedar.TPE.Response}
    (hwf : full.validateWellFormed = .ok ())
    (hwfs : sliced.validateWellFormed = .ok ())
    (hslice : sliced.IsActionSliceOf full preq.action)
    (hnolits : full.noActionLiteralsInConditions policies = true)
    (hnoistys : full.noActionTypeTestsInConditions policies = true)
    (hnoacttys : full.noActionTypedAttrs = true)
    (henv : validatePartialRequest sliced preq = .ok envS)
    (hguard :
      (entitiesIsValid envS.schema pes &&
        (pes.ancestors preq.action).isSome) = true)
    (hbase : TPE.isAuthorized full policies preq pes = .ok rf) :
    ∃ rs,
      TPE.isAuthorizedPartialWithSlicedPolicies sliced policies preq pes = .ok rs ∧
      rs.SliceRefines rf :=
  CrossSchema.isAuthorizedPartialWithSlicedPolicies_refines_full
    hwf hwfs hslice hnolits hnoistys hnoacttys henv hguard hbase

end Cedar.Thm
