/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Spec.Entities
import Cedar.Spec.PartialValue

/-!
This file defines Cedar partial-entities structures.
-/

namespace Cedar.Spec

open Except
open Cedar.Data

/--
Represents the information about one entity.

Currently, this allows attrs to be known-to-exist-but-unknown-value,
but does not allow attrs to be unknown-whether-they-exist-entirely.
(the result of `e has attr` is never a residual for an `e` that is known to exist.)

Currently, this does not allow any unknowns about ancestor information.
All ancestor information must be fully concrete.
-/
structure PartialEntityData where
  attrs : Map Attr RestrictedPartialValue
  ancestors : Set EntityUID

def EntityData.asPartialEntityData (d : EntityData) : PartialEntityData :=
  {
    attrs := d.attrs.mapOnValues RestrictedPartialValue.value,
    ancestors := d.ancestors,
  }

/--
Represents the information about all entities.

Currently, this does not allow it to be unknown whether an entity exists.
Either it exists (and we have a PartialEntityData) or it does not.
-/
abbrev PartialEntities := Map EntityUID PartialEntityData

def PartialEntities.ancestors (es : PartialEntities) (uid : EntityUID) : Result (Set EntityUID) := do
  let d ← es.findOrErr uid .entityDoesNotExist
  ok d.ancestors

def PartialEntities.ancestorsOrEmpty (es : PartialEntities) (uid : EntityUID) : Set EntityUID :=
  match es.find? uid with
  | some d => d.ancestors
  | none   => Set.empty

def PartialEntities.attrs (es : PartialEntities) (uid : EntityUID) : Result (Map Attr RestrictedPartialValue) := do
  let d ← es.findOrErr uid .entityDoesNotExist
  ok d.attrs

def PartialEntities.attrsOrEmpty (es : PartialEntities) (uid : EntityUID) : Map Attr RestrictedPartialValue :=
  match es.find? uid with
  | some d => d.attrs
  | none   => Map.empty

deriving instance Inhabited for PartialEntityData

def Entities.asPartialEntities (es : Entities) : PartialEntities :=
  es.mapOnValues EntityData.asPartialEntityData

instance : Coe Entities PartialEntities where
  coe := Entities.asPartialEntities

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new PartialEntityData.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `PartialEntityData` will still contain some unknowns.
-/
def PartialEntityData.subst (d : PartialEntityData) (subsmap : Map String RestrictedPartialValue) : PartialEntityData :=
  {
    attrs := d.attrs.mapOnValues (RestrictedPartialValue.subst · subsmap),
    ancestors := d.ancestors,
  }

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing an EntityData.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).
-/
def PartialEntityData.fullSubst (d : PartialEntityData) (subsmap : Map String Value) : Option EntityData := do
  let attrs' ← d.attrs.mapMOnValues (RestrictedPartialValue.fullSubst · subsmap)
  some {
    attrs := attrs',
    ancestors := d.ancestors,
  }

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new PartialEntities.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `PartialEntities` will still contain some unknowns.
-/
def PartialEntities.subst (es : PartialEntities) (subsmap : Map String RestrictedPartialValue) : PartialEntities :=
  es.mapOnValues (PartialEntityData.subst · subsmap)

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing an Entities.
  This means that `subsmap` must contain mappings for all the unknowns (or this
  function will return `none`).
-/
-- TODO: turning a PartialEntities into an Entities might require adding new entities,
-- how do we account for that?
def PartialEntities.fullSubst (es : PartialEntities) (subsmap : Map String Value) : Option Entities :=
  es.mapMOnValues (PartialEntityData.fullSubst · subsmap)

end Cedar.Spec
