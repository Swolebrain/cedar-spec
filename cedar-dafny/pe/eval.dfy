include "def.dfy"
include "util.dfy"
include "environment.dfy"
include "engine.dfy"
include "../def/core.dfy"
include "../def/base.dfy"
include "../def/engine.dfy"
include "../def/std.dfy"

module pe.eval {
  import opened definition
  import ce = def.engine
  import def.core
  import def.base
  import opened def.std
  import util
  import opened environment
  import opened engine

  ghost function getTypedValue<T>(r: base.Result<core.Value>, conv: core.Value -> base.Result<T>): base.Result<core.Value> {
    var v :- r;
    var _ :- conv(v);
    Ok(v)
  }

  lemma MakeErrorValueIsErr(env: Environment, s: core.EntityStore)
    requires env.wellFormed()
    ensures var r := PartialEvaluator.makeErrorValue(); env.interpret(r, s).Err? {
    calc {
      env.interpret(PartialEvaluator.makeErrorValue(), s);
    ==
      calc {
        env.interpret(Residual.Record([]), s);
      ==
        Ok(core.Value.Record(map[]));
      }
      Err(base.AttrDoesNotExist);
    }
  }

  lemma InterpretResidualAndErr(env: Environment, r1: Residual, r2: Residual, s: core.EntityStore)
    requires env.wellFormed()
    requires env.interpret(r1, s).Err? || core.Value.asBool(env.interpret(r1, s).value).Err?
    ensures env.interpret(Residual.And(r1, r2), s).Err? {

  }

  lemma EnvInterpretResidualTrue(env: Environment, r1: Residual, r2: Residual, s: core.EntityStore)
    requires env.wellFormed()
    requires var v1 := env.interpret(r1, s); v1.Ok? && v1.value == core.Value.Bool(true)
    ensures env.interpret(Residual.And(r1, r2), s) == getTypedValue(env.interpret(r2, s), core.Value.asBool) {
    calc == {
      core.Value.asBool(env.interpret(r1, s).value);
      Ok(true);
    }
    calc == {
      env.interpret(Residual.And(r1, r2), s);
      match env.interpret(r1, s) {
        case Err(err1) => Err(err1)
        case Ok(v1) => match(core.Value.asBool(v1)) {
          case Ok(b1) => if b1 then
            match env.interpret(r2, s) {
              case Ok(v2) => core.Value.asBool(v2).Map(_ => v2)
              case Err(err2) => Err(err2)
            }
          else Ok(core.Value.Bool(false))
          case Err(tyerr1) => Err(tyerr1)
        }
      };
    }
  }

  lemma InterpretRestrictedResidualSet(rs: seq<Residual>, env: Environment, s: core.EntityStore)
    requires forall r | r in rs :: r.restricted?()
    requires env.wellFormed()
    ensures env.interpretSet(rs, s) == env.interpretSet(rs, core.EntityStore(map[]))
  {
    if |rs| == 0 {

    } else {
      InterpretRestrictedResidual(rs[0], env, s);
    }
  }

  lemma InterpretRestrictedResidualRecord(bs: seq<(core.Attr, Residual)>, env: Environment, s: core.EntityStore)
    requires forall b | b in bs :: b.1.restricted?()
    requires env.wellFormed()
    ensures env.interpretRecord(bs, s) == env.interpretRecord(bs, core.EntityStore(map[]))
  {
    if |bs| == 0 {

    } else {
      InterpretRestrictedResidual(bs[0].1, env, s);
    }
  }

  lemma InterpretRestrictedResidualList(rs: seq<Residual>, env: Environment, s: core.EntityStore)
    requires forall r | r in rs :: r.restricted?()
    requires env.wellFormed()
    ensures env.interpretList(rs, s) == env.interpretList(rs, core.EntityStore(map[])) {
    if |rs| == 0 {

    } else {
      InterpretRestrictedResidual(rs[0], env, s);
    }
  }

  lemma InterpretRestrictedResidual(r: Residual, env: Environment, s: core.EntityStore)
    requires r.restricted?()
    requires env.wellFormed()
    ensures env.interpret(r, s) == env.interpret(r, core.EntityStore(map[]))
  {
    match r {
      case Concrete(_) =>
      case Unknown(_) =>
      case Set(rs) => InterpretRestrictedResidualSet(rs, env, s);
      case Record(bs) => InterpretRestrictedResidualRecord(bs, env, s);
      case Call(_, args) => InterpretRestrictedResidualList(args, env, s);
    }
  }

  lemma PEInterpretSeqErr(es: seq<definition.Expr>, pe: PartialEvaluator)
    requires pe.interpretSeq(es).Err?
    ensures exists e | e in es :: pe.interpret(e).Err?
  {

  }

  lemma CEInterpretSetErr(es: seq<core.Expr>, ce: ce.Evaluator)
    requires exists e | e in es :: ce.interpret(e).Err?
    ensures ce.interpretSet(es).Err? {

  }

  lemma CEInterpretSetOk(es: seq<core.Expr>, ce: ce.Evaluator)
    requires ce.interpretSet(es).Ok?
    ensures forall e | e in es :: ce.interpret(e).Ok? {

  }

  lemma CEInterpretSetMapReduce(es: seq<core.Expr>, ce: ce.Evaluator)
    ensures ce.interpretSet(es) == util.CollectToSet(util.Map(es, ce.interpret))
  {
    if |es| > 0 {
      assert util.Map(es, ce.interpret) == [ce.interpret(es[0])] + util.Map(es[1..], ce.interpret);
    }
  }

  lemma EnvInterpretSetMapReduce(rs: seq<Residual>, env: environment.Environment, s: core.EntityStore)
    requires env.wellFormed()
    ensures env.interpretSet(rs, s) == util.CollectToSet(util.Map(rs, r => env.interpret(r, s)))
  {
    if |rs| == 0 {

    } else {
      assert util.Map(rs, r => env.interpret(r, s)) == [env.interpret(rs[0], s)] + util.Map(rs[1..], r => env.interpret(r, s));
    }
  }

  lemma PEInterpretSeqOk(es: seq<definition.Expr>, pe: PartialEvaluator)
    requires pe.interpretSeq(es).Ok?
    ensures forall e | e in es :: pe.interpret(e).Ok?
  {

  }

  lemma PEInterpretSetMapReduce(es: seq<definition.Expr>, pe: PartialEvaluator)
    ensures pe.interpretSeq(es) == util.CollectToSeq(util.Map(es, pe.interpret))
  {
    if |es| > 0 {
      assert util.Map(es, pe.interpret) == [pe.interpret(es[0])] + util.Map(es[1..], pe.interpret);
    }
  }

  lemma PEInterpretSet(e: definition.Expr, PE: PartialEvaluator, env: environment.Environment, s: core.EntityStore)
    requires e.Set?
    requires env.wellFormed()
    requires PE.interpretSeq(e.es).Ok?
    requires !forall r | r in PE.interpretSeq(e.es).value :: r.Concrete?
    ensures (forall i: nat | i < |e.es| :: PE.interpret(e.es[i]).Ok?) && env.interpret(PE.interpret(e).value, s) == util.CollectToSet(util.Map(e.es, e' requires PE.interpret(e').Ok? => env.interpret(PE.interpret(e').value, s))).Map(v => core.Value.Set(v)) {
    PEInterpretSeqOk(e.es, PE);
    assert forall e' | e' in e.es :: PE.interpret(e').Ok?;
    assert forall i: nat | i < |e.es| :: PE.interpret(e.es[i]).Ok?;
    PEInterpretSetMapReduce(e.es, PE);
    util.CollectToSeqOk(util.Map(e.es, PE.interpret));
    var peI := e' requires PE.interpret(e').Ok? => PE.interpret(e').value;
    calc == {
      PE.interpretSeq(e.es).value;
      util.CollectToSeq(util.Map(e.es, PE.interpret)).value;
      util.Map(util.Map(e.es, PE.interpret), (r: definition.Result<Residual>) requires r.Ok? => r.value);
      util.Map(e.es, peI);
    }
    EnvInterpretSetMapReduce(util.Map(e.es, peI), env, s);
    calc == {
      env.interpretSet(PE.interpretSeq(e.es).value, s);
      env.interpretSet(util.Map(e.es, peI), s);
      util.CollectToSet(util.Map(util.Map(e.es, peI), r => env.interpret(r, s)));
    }
    assert util.CollectToSet(util.Map(e.es, e' requires PE.interpret(e').Ok? => env.interpret(PE.interpret(e').value, s))) == util.CollectToSet(util.Map(util.Map(e.es, peI), r => env.interpret(r, s))) by {
      util.MapCompose(e.es, peI, r => env.interpret(r, s));
      assert util.Map(util.Map(e.es, peI), r => env.interpret(r, s)) == util.Map(e.es, e' requires PE.interpret(e').Ok? => env.interpret(PE.interpret(e').value, s));
    }
    calc == {
      env.interpret(PE.interpret(e).value, s);
      env.interpret(Residual.Set(PE.interpretSeq(e.es).value), s);
      env.interpretSet(PE.interpretSeq(e.es).value, s).Map(v => core.Value.Set(v));
    }
  }

  lemma CEInterpretSet(e: definition.Expr, CE: ce.Evaluator, env: environment.Environment)
    requires e.Set?
    requires env.wellFormed()
    ensures CE.interpret(env.replaceUnknownInExpr(e)) ==
            util.CollectToSet(
              util.Map(
                e.es,
                e' requires e' < e => CE.interpret(env.replaceUnknownInExpr(e')))).Map(v => core.Value.Set(v)) {
    CEInterpretSetMapReduce(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e')), CE);
    util.MapCompose(e.es, e' requires e' < e => env.replaceUnknownInExpr(e'), CE.interpret);
    assert util.Map(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e')), CE.interpret) == util.Map(e.es, e' requires e' < e => CE.interpret(env.replaceUnknownInExpr(e')));
    calc == {
      CE.interpret(env.replaceUnknownInExpr(e));
      CE.interpret(core.Expr.Set(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e'))));
      CE.interpretSet(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e'))).Map(v => core.Value.Set(v));
      util.CollectToSet(util.Map(util.Map(e.es, e' requires e' < e => env.replaceUnknownInExpr(e')), CE.interpret)).Map(v => core.Value.Set(v));
      util.CollectToSet(util.Map(e.es, e' requires e' < e => CE.interpret(env.replaceUnknownInExpr(e')))).Map(v => core.Value.Set(v));
    }

  }
}
