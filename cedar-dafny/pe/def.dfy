include "../def/core.dfy"
include "../def/std.dfy"
include "../def/util.dfy"

module pe.definition {
  import opened def.core
  import opened def.base
  import opened def.std
  import opened def.util

  datatype Unknown = Unknown(name: string)

  type Error = base.Error
  type Result<T> = std.Result<T, Error>

  datatype Expr =
    PrimitiveLit(Primitive) |
    Var(Var) |
    If(Expr, Expr, Expr) |
    And(Expr, Expr) | // shortcircuiting &&
    Or(Expr, Expr)  | // shortcircuiting ||
    UnaryApp(UnaryOp, Expr) |
    BinaryApp(BinaryOp, Expr, Expr) |
    GetAttr(Expr, Attr) |
    HasAttr(Expr, Attr) |
    Set(seq<Expr>) |
    Record(fvs: seq<(Attr, Expr)>) |
    Call(name: Name, args: seq<Expr>) |
    Unknown(u: Unknown)

  // Rust implementation defines it as something like
  //   datatype PartialValue =
  //     Concrete(v: core.Value) |
  //     Partial(e: Expr)
  // The problem with this implementation is that it requires conversion from `Value` to `Expr`.
  // For instance, when evaluating `1 + unknown("x")`, we get `Concrete(Int(1)` for LHS and `Uknown("x")` for RHS.
  // To build a `Partial` value, we need to convert the first value into an `Expr`.
  datatype Residual =
    Concrete(v: core.Value) |
    If(Residual, Residual, Residual) |
    And(Residual, Residual) |
    Or(Residual, Residual) |
    UnaryApp(UnaryOp, Residual) |
    BinaryApp(BinaryOp, Residual, Residual) |
    GetAttr(Residual, Attr) |
    HasAttr(Residual, Attr) |
    Set(seq<Residual>) |
    Record(fvs: seq<(Attr, Residual)>) |
    Call(name: Name, args: seq<Residual>) |
    Unknown(u: Unknown) {
    static function fromOptionalEntity(eu: OptionalEntity): Residual {
      match eu {
        case Left(e) => Concrete(Primitive(Primitive.EntityUID(e)))
        case Right(u) => Residual.Unknown(u)
      }
    }
    static function fromRecord(r: Record): Residual {
      if (forall v | v in r.Values :: v.Concrete?) then
        Concrete(core.Value.Record(map a : Attr | a in r.Keys :: r[a].v))
      else
        Residual.Record(RecordToSequence(r))

    }
  }

  type Record = map<Attr, Residual>
  type OptionalEntity = Either<EntityUID, Unknown>
  datatype Request =
    Request(principal: OptionalEntity,
            action: OptionalEntity,
            resource: OptionalEntity,
            context: Record)

  datatype EntityData = EntityData(attrs: Record, ancestors: set<EntityUID>)

  datatype EntityStore = EntityStore(
    entities: map<EntityUID, EntityData>)
  {
    // Can also be used just to test whether an entity exists in the store.
    function getEntityAttrs(uid: EntityUID): base.Result<Record> {
      if uid in entities.Keys then
        Ok(entities[uid].attrs)
      else
        Err(EntityDoesNotExist)
    }

    predicate entityIn(child: EntityUID, ancestor: EntityUID)
      requires child in entities.Keys
    {
      ancestor in entities[child].ancestors
    }
  }
}
