(* Copyright (C) 2009,2011 Matthew Fluet.
 * Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor GvnPre (S: SSA_TRANSFORM_STRUCTS): SSA_TRANSFORM =
struct

open S

(* Counter to provide ids for VExp.value *)
structure Counter = 
struct
    datatype t = ValNum | StatementsAdded | PartialRedundancy | StatementsEliminated
    val valNum = ref 0
    val statementsAdded = ref 0
    val statementsEliminated = ref 0
    val partialRedundancies = ref 0
fun nextValNum counter =
        case counter of
            ValNum => (valNum := !valNum + 1 ; !valNum)
        |   StatementsAdded => (statementsAdded := !statementsAdded + 1 ; !statementsAdded)
        |   PartialRedundancy => (partialRedundancies := !partialRedundancies + 1 ; !partialRedundancies)
        |   StatementsEliminated => (statementsEliminated := !statementsEliminated + 1 ; !statementsEliminated)
end
    
fun diagWithLabel label s =
  Control.diagnostics
      (fn display =>
          let open Layout
          in
              display (seq [Label.layout label, str ": ", str s])
          end)

fun diag s funcName =
  Control.diagnostics
      (fn display =>
          let open Layout
          in
              display (seq [str funcName, str ": ", str s])
          end)

structure VExp =
struct

    datatype t =
             VConst of Const.t
           | VPrimApp of {prim: Type.t Prim.t,
                args: value vector,
                            targs: Type.t vector}
           | VConApp of {args: value vector,
                          con: Con.t}
           | VSelect of {offset: int,
                          tuple: value}
           | VTuple of value vector
           | VVar of Var.t
    and value = Value of {vexps: t list ref, id: int, vType: Type.t}

    fun newValue () = Value {vexps=(ref []), id = Counter.nextValNum Counter.ValNum, vType = Type.unit}
    fun nullValue () = Value {vexps=(ref []), id = (~1), vType = Type.unit}

    fun valueEquals(xs: value, xs': value) =
        let
            val Value {id=id,...} = xs
            val Value {id=id',...} = xs'
        in
            id=id'
        end

    fun primValueListEquals (xs, xs') = Vector.equals (xs, xs', valueEquals)
    and equals (e: t, e': t): bool =
    case (e, e') of
            (VConst c, VConst c') => Const.equals (c, c')
          | (VPrimApp {prim, args, ...},
             VPrimApp {prim = prim', args = args',...}) =>
                Prim.equals (prim, prim') andalso primValueListEquals (args, args')
          | (VConApp {con, args},
             VConApp {con = con', args = args'}) =>
                Con.equals (con, con') andalso primValueListEquals (args, args')
          | (VSelect {offset,tuple},
             VSelect {offset = offset', tuple = tuple'}) => Int.equals(offset,offset') andalso valueEquals(tuple,tuple')
          | (VTuple xs, VTuple xs') => primValueListEquals (xs, xs')
          | (VVar x, VVar x') => Var.equals (x, x')
          | _ => false

    fun layoutValue v =
        let
            open Layout
        in
            case v of
                Value {id=id,...} => Layout.str (Int.toString id)
                (*seq  [(seq [str "", List.layout layout  (!vexps) ]) , 
                    Layout.str (Int.toString id), (Type.layout vType)]*)
        end

    and layout e =
    let
        open Layout
        fun layoutTuple xs = Vector.layout (fn v => layoutValue v) xs
    in
        case e of
            VConst c => Const.layout c
          | VPrimApp {prim=prim,targs=targs,args=args} =>
                seq [Prim.layout prim,
                        if !Control.showTypes
                        then if 0 = Vector.length targs
                             then empty
                             else Vector.layout Type.layout targs
                        else empty,
                            seq [str " ", layoutTuple args]]
          | VConApp {con=con,args=args} => 
                seq [Con.layout con,
                        seq [str " ", layoutTuple args]]
          | VSelect {offset=offset,tuple=tuple} => 
                seq [str "#", Int.layout offset, str " ",
                       layoutValue tuple]
          | VTuple xs => seq [str " ", layoutTuple xs]
          | VVar x => Var.layout x
    end

    local
        val newHash = Random.word
        val primApp = newHash ()
        val conApp = newHash ()
        val tuple = newHash ()
        val select = newHash ()

        fun hasher v =
          let
              val Value {id=id,...} = v
          in
              Word.fromInt id
          end

        fun hashValueList (xs: value vector, w: Word.t): Word.t =
            Vector.fold (xs, w, fn (x, w) => Word.xorb (w, Word.xorb (w, hasher x)))
    in
        val hash  =
         fn (VConst c) => Const.hash c
          | (VPrimApp {args, ...}) => hashValueList (args, primApp)
          | (VConApp {args,...}) => hashValueList (args, conApp)
          | (VSelect {offset,tuple}) => Word.xorb (select, (hasher tuple) + Word.fromInt offset)
          | (VTuple xs) => hashValueList (xs, tuple)
          | (VVar x) => Var.hash x
    end

    val hash = hash

end

open Exp Transfer VExp Counter

structure ValTable =
struct
(* Keep a hash table of canonicalized Exps that are in scope. *)
    val table: {hash: word, vexp: VExp.t, values: VExp.value } HashSet.t =
        HashSet.new {hash = #hash}

    fun sort args =
        let
            val ls = Vector.toList args
            fun le (v,v') = case (v,v') of
                                ((VExp.Value {id=id,...}), (VExp.Value {id=id',...})) => (id <= id')
        in
            Vector.fromList (List.insertionSort (ls,le))
        end

    fun canon vexp = case vexp of
             VPrimApp {prim=prim,args=args,targs=targs} => if (Prim.isCommutative prim)
                                       then VPrimApp {prim=prim,args = sort args, targs=targs}
                                       else vexp
            | VConApp {con=con,args=args} => VConApp {con=con, args = args}
            | VSelect {offset=offset,tuple=tuple} => VSelect {offset=offset,tuple=tuple}
            | VTuple xs => VTuple (xs)
            | _ => vexp

    fun lookup vexp =
        let
            val vexp = canon vexp
        in
            HashSet.peek
              (table,VExp.hash vexp,
               fn {vexp = vexp', ...} => VExp.equals (vexp, vexp'))
        end

    fun lookupOrAddHelper (value, vexp, id, ty) =
        let
            val hash = VExp.hash vexp
        in
          HashSet.lookupOrInsert
              (table, hash,
               fn {vexp = vexp', ...} => VExp.equals (vexp, vexp'),
               fn () => {vexp = vexp,
                 hash = hash,
                 values = (Value {vexps = value, id = id, vType = ty})})
        end

    fun lookupOrAdd vexp ty =
        let
            val vexp = canon vexp
            val x = lookup vexp
        in
            case x of
              NONE  => lookupOrAddHelper(ref [vexp], vexp, nextValNum ValNum, ty)
            | SOME x => x
        end

    fun add (vexp, values, id, ty) =
        let
            val vexp = canon vexp
            val () = List.push(values, vexp)
            val _ = lookupOrAddHelper(values, vexp, id, ty)
        in
            ()
        end
end
    
structure LabelInfo =
struct
    datatype t = T of {dom: Label.t option ref,
                       predecessor: Block.t list ref,
                       successor:  Block.t list ref,
                       tmpGen: Var.t list ref,
                       killGen: Var.t list ref,
                       expGen: VExp.t list ref,
                       phiGen: Var.t list ref,
                       availOut: VExp.t list ref,
                       newSets: VExp.t list ref,
                       availIn: VExp.t list ref,
                       statementsGen: Statement.t list ref,
                       argsGen: (Var.t * Type.t) list ref,
                       gotoArgsGen: Var.t list ref,
                       anticIn: VExp.t list ref}

    fun new () = T {dom = ref NONE,
                    predecessor = ref [],
                    successor = ref [],
                    tmpGen = ref [],
                    killGen = ref [],
                    expGen = ref [],
                    phiGen = ref [],
                    availOut = ref [],
                    newSets = ref [],
                    availIn = ref [],
                    statementsGen = ref [],
                    argsGen = ref [],
                    gotoArgsGen = ref [],
                    anticIn = ref []}

    (* convenience functions for extracting components *)
    local
        fun make f (T r) = f r
        fun make' f = (make f, ! o (make f))
    in
        val (dom', dom) = make' #dom
        val (predecessor', predecessor) = make' #predecessor
        val (successor',successor) = make' #successor
        val (tmpGen', tmpGen) = make' #tmpGen
        val (killGen', killGen) = make' #killGen
        val (expGen', expGen) = make' #expGen
        val (phiGen', _) = make' #phiGen
        val (availOut', availOut) = make' #availOut
        val (newSets' , newSets) = make' #newSets
        val (_, _) = make' #availIn
        val (statementsGen',statementsGen) = make' #statementsGen
        val (argsGen',argsGen) = make' #argsGen
        val (gotoArgsGen',gotoArgsGen) = make' #gotoArgsGen
        val (anticIn', anticIn) = make' #anticIn
    end
end

fun transform (Program.T {globals, datatypes, functions, main}) =
    let
        val globalAvailOut = ref []
        val {get = getLabelInfo, ...} =
             Property.get(Label.plist, Property.initFun (fn _ => LabelInfo.new ()))
        fun doNonFunctional(v, label, ty) =
            let
                val () = ValTable.add(VVar v,ref [], nextValNum ValNum, ty)
                val () = List.push(LabelInfo.killGen' (getLabelInfo label), v)
                val () = List.push(LabelInfo.tmpGen' (getLabelInfo label), v)
            in
                ()
            end

    fun lookUpAndCheckExp(vexp,vexp') =
      let
              val v = ValTable.lookup vexp
              val v' = ValTable.lookup vexp'
          in
              case (v,v') of
                  (SOME {values=value,...},SOME {values=value',...}) => VExp.valueEquals(value,value')
                | (_,_) => false
          end

    fun valInsert vs vexp =
            if List.contains(!vs, vexp, lookUpAndCheckExp)
            then ()
            else List.push(vs,ValTable.canon vexp)

    fun valReplace lst l =
     lst := List.map(!lst, fn l' => if lookUpAndCheckExp(l,l')
                                              then l
                                              else l')

    fun handleFunctionArgs args label =
        let
            val () = Vector.foreach(args, fn (arg,ty) => 
                let
                    val () = ValTable.add(VVar arg,ref [], nextValNum ValNum, ty)
                    val () = (valInsert (LabelInfo.availOut' (getLabelInfo label)) (VVar arg))
                 in
                 ()
                 end)
        in
            ()
        end
    fun handlePhiCondtions(v, label, ty) =
        let
            val () = ValTable.add(VVar v,ref [], nextValNum ValNum, ty)
            val () = List.push(LabelInfo.phiGen' (getLabelInfo label), v)
            val () = (valInsert (LabelInfo.availOut' (getLabelInfo label)) (VVar v))
        in
            ()
        end

    fun handleStatements(s, label) =
        let
            val Statement.T {var=var, exp=exp, ty=ty} = s
            val () =
            (case var of
                 NONE => ()
               | SOME var' =>
               let
                      fun doFunctional exp args = 
                    let
                        val {values = primValue,...} = ValTable.lookupOrAdd exp ty
                        val (Value {vexps = values,id = id,...}) = primValue
                        val () = ValTable.add(VVar var', values, id, ty)
                        val _ = Vector.map(args, fn arg => (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VVar arg) ))
                        val () = (valInsert (LabelInfo.expGen' (getLabelInfo label)) exp)
                        val () = List.push(LabelInfo.tmpGen' (getLabelInfo label), var')
                    in
                    ()
                    end
                    
                    fun valueChanger arg = case (ValTable.lookup (VVar arg)) of
                                                        SOME {values = value,...} => value
                                                      | NONE =>  (VExp.newValue ()) (*filler will never happen*)
                    
                    fun valueList args = Vector.map(args, fn arg =>
                                                    valueChanger arg)
                in
                    (case exp  of
                       Var v =>
                       (let
                           val (vexps,id) = case (ValTable.lookup (VVar v)) of
                                                SOME {values=value,...} => (case value of
                                                                                Value {vexps=vexps,id=id,...} => (vexps,id))
                                              | NONE => (ref [], nextValNum ValNum)
                           val () = ValTable.add(VVar var', vexps, id, ty)
                           val () = (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VVar v))
                           val () = List.push(LabelInfo.tmpGen' (getLabelInfo label), var')
                        in
                            ()
                        end)
                    |  Const c =>
                       (let
                        val {values = primValue,...} = ValTable.lookupOrAdd (VConst c) ty
                        val (Value {vexps = values,id = id,...}) = primValue
                        val () = ValTable.add(VVar var', values, id, ty)
                        val () = (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VConst c))
                        val () = List.push(LabelInfo.tmpGen' (getLabelInfo label), var')
                            in
                            ()
                        end)
                    | PrimApp {args=args, prim=prim,targs=targs} =>
                       (let
                            val isFunctional = Prim.isFunctional prim
                        in
                            if isFunctional
                            then (let
                                    val exp = VPrimApp {args = valueList args, prim = prim, targs = targs}
                                    val () = doFunctional exp args
                                in
                                    ()
                                end)
                            else (case Prim.name prim of
                                     Prim.Name.Array_array =>
                                        let
                                           val arr = var'
                                           val arrTy = ty
                                           val eltTy = Vector.sub (targs, 0) (* = Type.deArray arrTy *)
                                           val len = Vector.sub (args, 0)
                                           val lenTy = Type.word (WordSize.seqIndex ())

                                           (* val arr: arrTy = Array_array[eltTy] (len) *)

                                           (* Create value for arr variable. *)
                                           val () = doNonFunctional (arr, label, arrTy)
                                           (* Lookup value for arr variable; must exist. *)
                                           val {values = arrValue, ...} =
                                              valOf (ValTable.lookup (VVar arr))
                                           (* Lookup value for len variable; must exist. *)
                                           val {values = lenValue, ...} =
                                              valOf (ValTable.lookup (VVar len))
                                           (* Add 'Array_length[eltTy] (arrValue)' vexp
                                            * to value of len variable. *)
                                           val arrLenPrim =
                                              VPrimApp {prim = Prim.arrayLength,
                                                        targs = Vector.new1 eltTy,
                                                        args = Vector.new1 arrValue}
                                           val Value {vexps = lenVExps, id = lenId, ...} =
                                              lenValue
                                           val () =
                                              ValTable.add (arrLenPrim, lenVExps, lenId, lenTy)
                                        in
                                           ()
                                        end
                                   | Prim.Name.Array_toVector =>
                                        let
                                           val vec = var'
                                           val vecTy = ty
                                           val eltTy = Vector.sub (targs, 0) (* = Type.deVector ty *)
                                           val arr = Vector.sub (args, 0)
                                           val lenTy = Type.word (WordSize.seqIndex ())

                                           (* val vec: vecTy = Array_toVector[eltTy] (arr) *)

                                           (* Create value for vec variable *)
                                           val () = doNonFunctional (vec, label, vecTy)
                                           (* Lookup value for vec variable; must exist. *)
                                           val {values = vecValue, ...} =
                                              valOf (ValTable.lookup (VVar var'))
                                           (* Lookup value for arr variable; must exist. *)
                                           val {values = arrValue, ...} =
                                              valOf (ValTable.lookup (VVar arr))
                                           (* Lookup value for 'Array_length[eltTy] (arrValue)' vexp;
                                            * may not exist. *)
                                           val arrLenPrim =
                                              VPrimApp {prim = Prim.arrayLength,
                                                        targs = Vector.new1 eltTy,
                                                        args = Vector.new1 arrValue}
                                           val {values = arrLenValue, ...} =
                                              ValTable.lookupOrAdd arrLenPrim lenTy
                                           (* Add 'Vector_length[eltTy] (vecValue)' vexp
                                            * to value of 'Array_length[eltTy] (arrValue)' vexp. *)
                                           val vecLenPrim =
                                              VPrimApp {prim = Prim.vectorLength,
                                                        targs = Vector.new1 eltTy,
                                                        args = Vector.new1 vecValue}
                                           val Value {vexps = arrLenVExps, id = arrLenId, ...} =
                                              arrLenValue
                                           val () =
                                              ValTable.add (vecLenPrim, arrLenVExps, arrLenId, lenTy)
                                        in
                                           ()
                                        end
                                   | _ => doNonFunctional (var', label, ty))
                       end)
                    | ConApp {con=con, args=args} => doFunctional (VConApp {con = con, args = valueList args}) args
                    | Select {offset=offset, tuple=tuple} => doFunctional (VSelect {offset = offset, tuple = valueChanger tuple}) (Vector.new1 tuple)
                    | Tuple args => doFunctional (VTuple (valueList args)) args
                    | _  => doNonFunctional (var', label, ty)
                   )
                end
            ) 
        in
            case var of
                NONE => ()
              | SOME var' => (valInsert (LabelInfo.availOut' (getLabelInfo label)) (VVar var'))
        end

        fun doBuildSets_Phase1 (block) =
            let
                val Block.T {args,label,statements,transfer} = block
                val _ = Vector.map(args, fn (a, ty) => handlePhiCondtions(a, label, ty))
                val _ = Vector.map(statements, fn s => handleStatements(s, label))
            in
                ()
            end

        fun loopTree_Phase1 (blockTree, parent, labelNode, nodeBlock, bfsBlockList) =
            let
                val Tree.T (block, children) = blockTree
                val () = List.push(bfsBlockList, block)
                val label = Block.label block
                val labelInfoObj = (getLabelInfo label)
                fun successors block = List.map(DirectedGraph.Node.successors (labelNode (Block.label block)), nodeBlock o DirectedGraph.Edge.to)
                val () = LabelInfo.successor' labelInfoObj := (successors block)
                val _ = List.map(LabelInfo.successor labelInfoObj, fn s =>
                                            let
                                                val succBlockLabel = Block.label s
                                            in
                                                List.push(LabelInfo.predecessor' (getLabelInfo succBlockLabel),block)
                                            end)
                val () = LabelInfo.dom' (getLabelInfo label) := parent

                val () = LabelInfo.availOut' labelInfoObj := (case (LabelInfo.dom labelInfoObj) of
                                          SOME domLabel => LabelInfo.availOut (getLabelInfo domLabel)
                                       |   NONE         => LabelInfo.availOut labelInfoObj)
                val () = doBuildSets_Phase1 (block)
                val () = Tree.Seq.foreach (children,fn child => loopTree_Phase1 (child, SOME label, labelNode, nodeBlock, bfsBlockList))
            in
                ()
            end

        fun diff(lst1, lst2) =
            let
                val {intersect=intersect,...} = (List.set {equals=VExp.equals, layout=VExp.layout})
                val intersection = intersect (lst1, lst2)
                fun difference [] _ = []
                  | difference (l::ls) (bs) = if (List.contains(bs, l, VExp.equals))
                                              then (difference ls bs)
                                              else (l::(difference ls bs))
            in
            (difference lst1 intersection)
        end
        fun clean(lst1, killGen) =
            let
                val killToVal = List.map(killGen, fn kill =>
                                    let
                                        val v = case (ValTable.lookup (VVar kill)) of
                                              NONE => ref (VExp.nullValue ())
                                             |SOME {values,...} => ref values
                                    in
                                        case (!v) of
                                            VExp.Value{id=id,...} => id
                                    end)

                fun allTrue ls = List.forall(ls, fn b => b)

                fun checkValue v = case v of
                           VExp.Value{vexps=vexps,id=id,...} => 
                                if List.contains(killToVal,id,Int.equals)
                                then false
                                else (allTrue (List.map((!vexps), fn vexp => isValid vexp)))

                and isValid vexp = case vexp of
                           (VPrimApp {args=args,...}) => 
                                let 
                                    val isValidList = (Vector.toList (Vector.map(args , fn a => checkValue a)))
                                    val result = allTrue isValidList
                                in
                                    result
                                end
                         | (VVar v) => if List.contains(killGen,v,Var.equals)
                                       then false
                                       else true
                         |  _ => true

                fun processedKills [] = []
                  | processedKills (l::ls) = (if(isValid l)
                                              then [l]@(processedKills ls)
                                              else (processedKills ls))
            in
                processedKills lst1
            end

    fun leader [] _ = []
          | leader (l::ls) value =  (case (ValTable.lookup l) of
                                                       NONE => leader ls value
                                                     | SOME {values = value',...} => 
                                                          if VExp.valueEquals(value, value')
                                                          then (
                                                               case l of
                                                               (VVar _) => [l]
                                                               | _ => leader ls value
                                                               )
                                                          else leader ls value)

        fun findLeader(anticIn, exp) =
            let
                val v = ValTable.lookup exp
            in
                case v of
            (SOME {values,...}) => leader anticIn values
         | NONE => [] 
            end

        fun someTrue ls = List.exists(ls, fn b => b)

        fun phiTranslate (lst, block, succBlock) =
            let
                val Block.T {transfer,...} = block
                val Block.T {args=fromVar',...} = succBlock
                val toVar' = case transfer of
                         Goto {args,...} => args
                       | _ => 
                            Vector.fromList []
                fun varToValue v = case (ValTable.lookup (VVar v)) of
                                       NONE => (VExp.nullValue ())(*Filler will never Happen*)
                                     | SOME {values,...} => values
                val toVar = Vector.toList toVar'
                val fromVar = List.map(Vector.toList fromVar', fn (arg,_) => arg)
                val toValue = List.map(toVar, fn arg => varToValue arg)
                val fromValue = List.map(fromVar, fn arg => varToValue arg)
                val {intersect=intersect,...} = (List.set {equals=VExp.valueEquals, layout=(fn v => layoutValue v)})
                
                fun translateExp args vexp = 
                    let
                         val intersection = intersect (Vector.toList args, fromValue)
                         fun translateArgs args =
                            Vector.map(args, fn arg =>
                              (case List.index(fromValue, fn arg' => VExp.valueEquals(arg,arg')) of
                                   NONE => arg
                                 | SOME i => (List.nth(toValue,i))
                              ))
                        val newVexp = case vexp of
                            (VPrimApp {prim = prim, args = args, targs = targs}) =>
                                (VPrimApp {prim = prim, args = (translateArgs args), targs = targs})
                            |(VConApp {con = con, args = args}) =>
                                (VConApp {con = con, args = (translateArgs args)})
                            |(VTuple args) => (VTuple (translateArgs args))
                            | _ => vexp
                     in
                         case intersection of
                             [] => vexp 
                           | _ => (let
                                      val () =  case ValTable.lookup(vexp) of 
                                                  NONE => ()
                                                 |SOME {values,...} => case values of
                                                                       VExp.Value{vType=vType,...} =>
                                                                              let 
                                                                                val _ = ValTable.lookupOrAdd newVexp vType
                                                                              in
                                                                               ()
                                                                              end
                                   in
                                     newVexp
                                   end)
                     end
                
                fun translate vexp = case vexp of
                             (VVar v) => (case List.index(fromVar, fn v' => Var.equals(v,v')) of
                                      NONE => vexp
                                    | SOME i => (VVar (List.nth(toVar,i)))
                                 )
                           | (VPrimApp {args = args, ...}) => translateExp args vexp
                           | (VConApp {args = args,...}) => translateExp args vexp
                           | (VTuple args) => translateExp args vexp
                           | x  => x
        in
            case transfer of
                Goto {...} => List.map(lst, translate)
              | _ => lst
        end

        fun handleSuccesors (block, childrenCount, children) =
            if childrenCount=1
            then
                let
                    val succBlock = List.first children
                    val succBlockLabel = Block.label succBlock
                in
                    phiTranslate (LabelInfo.anticIn (getLabelInfo (succBlockLabel)), block, succBlock)
                end
            else if (childrenCount>1)
            then
                (let
                      val worklist = ref children
                      val block = List.pop worklist
                      val label = Block.label block
                      val ANTIC_OUT = ref []
                      val () = ANTIC_OUT := LabelInfo.anticIn (getLabelInfo label)
                      fun handleWorkList ANTIC_OUT (ref []) = !ANTIC_OUT
                        | handleWorkList ANTIC_OUT worklist =
                          (let
                                val block = List.pop worklist
                                val b'label = Block.label block
                                val () =
                                List.foreach(!ANTIC_OUT, fn e =>
                                                let
                                                    val {remove=remove,...} = (List.set {equals=VExp.equals, layout=VExp.layout})
                                                    val () =
                                                        case findLeader (LabelInfo.anticIn (getLabelInfo b'label), e)  of
                                                            [] => ANTIC_OUT := (remove (!ANTIC_OUT, e))
                                                          | _ => ()
                                                in
                                                    ()
                                                end
                                            )
                            in
                                (handleWorkList ANTIC_OUT worklist)
                            end)
                  in
                    (handleWorkList ANTIC_OUT worklist)
                  end)
            else []

        fun loopTree_Phase2 (block) =
            let
                val label = Block.label block
                val labelInfoObj = (getLabelInfo label)
                val old = (LabelInfo.anticIn labelInfoObj)
                val ANTIC_OUT = ref []
                val blockSuccessors = LabelInfo.successor labelInfoObj
                val () = ANTIC_OUT := handleSuccesors (block, List.length blockSuccessors,  blockSuccessors)
                val tmpList = List.map(LabelInfo.tmpGen labelInfoObj, fn v => (VVar v))
                val S = diff(!ANTIC_OUT, tmpList)
                val () = LabelInfo.anticIn' labelInfoObj := diff(LabelInfo.expGen labelInfoObj, tmpList)
                val () = List.foreach(S, fn s =>
                            let
                                val leader = findLeader(LabelInfo.expGen labelInfoObj, s)
                                val () = case leader of
                                            [] => (valInsert (LabelInfo.anticIn' labelInfoObj) s)
                                          |  _ => ()
                            in
                                ()
                            end
                         )
                val () = LabelInfo.anticIn' (getLabelInfo label) := clean(LabelInfo.anticIn (getLabelInfo label), 
                                                                          (LabelInfo.killGen (getLabelInfo label)))
            in
                if (List.equals(old,(LabelInfo.anticIn (getLabelInfo label)),VExp.equals))
                then false
                else true
            end

        fun doBuildSets_Phase2 (dfsBlockList) =
            let
                val isChanged = if someTrue(List.map(dfsBlockList, fn block => loopTree_Phase2 block))
                                then doBuildSets_Phase2 (dfsBlockList)
                                else false
            in
                isChanged
            end

        fun eliminateStatements s block =
            let
                val Statement.T {var=var, exp=exp, ty=ty} = s
                val label = Block.label block
                val labelInfoObj = (getLabelInfo label)
                (*Complete logic from commonSubexp pass just to compare the performmance of gvnPre*)
                (* From mlton/ssa/commonSubexp.fun*)
                fun commonSubexpCanonLogic exp = 
                    case exp of
                     PrimApp {prim, targs, args} =>
                       let
                          fun arg i = Vector.sub (args, i)
                          fun canon2 () =
                             let
                                val a0 = arg 0
                                val a1 = arg 1
                             in
                                (* What we really want is a total orderning on
                                 * variables.  Since we don't have one, we just use
                                 * the total ordering on hashes, which means that
                                 * we may miss a few cse's but we won't be wrong.
                                 *)
                                if Var.hash a0 <= Var.hash a1
                                   then (a0, a1)
                                else (a1, a0)
                             end
                          datatype z = datatype Prim.Name.t
                       in
                          if Prim.isCommutative prim
                             then PrimApp {args=(Vector.new2 (canon2 ())),targs=targs,prim=prim}
                          else
                             if (case Prim.name prim of
                                    IntInf_add => true
                                  | IntInf_andb => true
                                  | IntInf_gcd => true
                                  | IntInf_mul => true
                                  | IntInf_orb => true
                                  | IntInf_xorb => true
                                  | _ => false)
                                then
                                   let
                                      val (a0, a1) = canon2 ()
                                   in PrimApp {args=(Vector.new3 (a0, a1, arg 2)),targs=targs,prim=prim}
                                   end
                             else exp
                       end
                    | _ => exp
                fun changeExp v = 
                    (let
                           val sList' = findLeader(LabelInfo.availOut labelInfoObj, VVar v)
                       in
                           (case sList' of
                            [] => exp
                          | [(VVar s')] =>   if VExp.equals(VVar s',VVar v)
                                     then exp
                                     else (let  
                                            val _ = nextValNum StatementsEliminated
                                          in (Var s') 
                                          end)
                          | _ => exp)
                       end)
            in
                (case var of
                 NONE => s
                   | SOME v => (case exp of
                                    PrimApp {prim = prim,...}=>
                                    (let
                                        val exp' =  if (Prim.isFunctional prim)
                                                    then changeExp v
                                                    else (case Prim.name prim of
                                                            Prim.Name.Array_array => changeExp v
                                                        | Prim.Name.Array_toVector => changeExp v
                                                        | _ =>exp)
                                        val exp'' = commonSubexpCanonLogic exp'
                                    in
                                        Statement.T {var=var, exp=exp'', ty=ty}
                                        (*normal gvnPre invocation*)
                                        (*Statement.T {var=var, exp=exp', ty=ty}*)
                                    end)
                                | Const c => 
                                    (case (findLeader (!globalAvailOut,VConst c)) of
                                              [VVar v'] => Statement.T {var = var, exp = (Var v'), ty = ty} 
                                              | _ => Statement.T {var = var, exp = changeExp v, ty = ty}) 
                                | ConApp {...} => Statement.T {var = var, exp = changeExp v, ty = ty}
                                | Select {...} => Statement.T {var = var, exp = changeExp v, ty = ty}
                                | Tuple _ => Statement.T {var = var, exp = changeExp v, ty = ty}
                                | _ => s)
                )
            end

        fun eliminate block =
            let
                val Block.T {args,label,statements,transfer} = block
                val statements' = Vector.map(statements, fn s => eliminateStatements s block)
            in
                Block.T {args=args, label=label, statements=statements', transfer=transfer}
            end

    fun doMergingBlock block v1opv2 new_stuff =
      let
          val label = Block.label block
          val labelInfoObj = (getLabelInfo label)
          val availKey = ref []
          val availValue = ref []
          val v1opv2Type = case ValTable.lookup(v1opv2) of
                                                         SOME {values=values,...} =>
                                                         (case values of
                                                          VExp.Value {vType=vType,...} => vType)
                                                       | NONE => Type.unit
          fun get(b) = (case List.index(!availKey, fn b' => Label.equals(b,b')) of
                                  NONE => NONE
                                | SOME i => SOME (List.nth(!availValue,i))
                             )
          
          
            fun change(_,_,[]) = []
            |   change(0, v, _::xs) =  v :: xs
            |   change(i, v, x::xs) =  if i < 0 
                                       then x::xs
                                       else  x :: change((i-1), v, xs)

         fun put(b,e) = (case List.index(!availKey, fn b' => Label.equals(b,b')) of
            NONE =>
                  let
                      val () = List.push(availKey,b)
                      val () = List.push(availValue,e)
                  in
                      ()
                  end
          | SOME i => availValue := change(i,e,!availValue)
                         )
                             
          val by_some = ref false
          val all_same = ref true
          val first_s = ref NONE
          val _ = List.foreach(LabelInfo.predecessor labelInfoObj, fn p =>
                                      let
                                          val predLabel = Block.label p
                                          val e' = List.first(phiTranslate([v1opv2],p,block))
										  val () = diagWithLabel predLabel (Layout.toString (VExp.layout e'))
                                          val () = diagWithLabel label (Layout.toString (VExp.layout v1opv2))
                                      in                                          
                                        (let
											val () = diagWithLabel predLabel (Layout.toString (List.layout VExp.layout (LabelInfo.availOut (getLabelInfo predLabel))))
                                            val e'' = findLeader(LabelInfo.availOut (getLabelInfo predLabel),e')
											val () = diag "leader after phitranslate " (Layout.toString (List.layout VExp.layout (e'')))
                                         in
                                            case e'' of
                                            [] => (let
                                                      val () = put(predLabel,e')
													  val () = diagWithLabel predLabel "putting the exp here"
                                                      val () = diagWithLabel predLabel (Layout.toString (VExp.layout e'))
                                                      val () = all_same := false
                                                  in
                                                    ()
                                                  end)
                                          | [l] => (let
                                                       val () = put(predLabel,l)
                                                       val () = by_some := true  
                                                       val () = LabelInfo.anticIn' (getLabelInfo label) := 
                                                                    List.remove(LabelInfo.anticIn (getLabelInfo label), 
                                                                                    fn a => VExp.equals(a,v1opv2))
                                                   in
                                                   case (!first_s) of
                                                       NONE => first_s := SOME l
                                                     | SOME first_s' => if VExp.equals(first_s',l)
                                                            then ()
                                                            else all_same := false
                                                   end)
                                          | _ => () 
                                        end)
                                      end)
          val tempValidator = ref true
          val () = if ((not (!all_same)) andalso !by_some)
               then (let
                    val _ = List.foreach(LabelInfo.predecessor labelInfoObj, fn p =>
                                let 
                                    val predLabel = Block.label p
                                    val e' = get(predLabel)
									val () = diagWithLabel predLabel "working on preds: adding new statements"
                                    fun insertExp args oldExp= 
                                      let
                                          fun buildPrimArgs [] = []
                                            | buildPrimArgs (l::ls) = 
                                                let
                                                    val leaderList = (leader (LabelInfo.availOut (getLabelInfo predLabel)) l)
													val () = diag "exp" (Layout.toString (VExp.layoutValue (l)))
													val () = diag "leader" (Layout.toString (List.layout VExp.layout (leaderList)))
                                                in
                                                case leaderList of
                                                  [VVar v] => v::(buildPrimArgs ls)
                                                | [VConst _] => (
                                                                 case (leader (!globalAvailOut) l) of
                                                                  [VVar v] => v::(buildPrimArgs ls)
                                                                  | _ => (buildPrimArgs ls)
                                                                )
                                                  | _ => (
                                                                 case (leader (!globalAvailOut) l) of
                                                                  [VVar v] => v::(buildPrimArgs ls)
                                                                  | _ => (buildPrimArgs ls)
                                                                )
                                                end
                                                
                                          
                                          val translatedArgs = Vector.fromList (buildPrimArgs (Vector.toList args))
                                          val () = if (Vector.length(translatedArgs)=Vector.length(args))
                                                   then ()
                                                   else tempValidator := false
                                        val () = if (!tempValidator) 
                                          then 
                                              let
                                                  val t = Var.newNoname ()
												  val () = diag "adding statement " ""
														  val () = diagWithLabel predLabel (Layout.toString (VExp.layout oldExp))
                                                  val _ = nextValNum StatementsAdded
                                                  val newExp = case oldExp of
                                                     VPrimApp {targs = targs, prim = prim, ...} =>
                                                        (PrimApp {args = translatedArgs, targs = targs, prim = prim})
                                                    | VConApp {con = con, ...} =>
                                                        (ConApp {con = con, args = translatedArgs})
                                                    | VTuple _ => Tuple translatedArgs
                                                    | VSelect {offset,...} => Select {offset=offset, tuple = Vector.sub(translatedArgs,0)}
                                                    | VVar v => Var v
                                                    | VConst c => Const c
                                                  val newStatement = Statement.T {exp = newExp, ty = v1opv2Type, var = (SOME t)}
												  val () = diag "statement: " (Layout.toString (Statement.layout newStatement))
                                                  val () = List.push(LabelInfo.statementsGen' (getLabelInfo predLabel),newStatement)
                                                  val () = case (ValTable.lookupOrAdd oldExp v1opv2Type) of
                                                       {values=values,...} =>
                                                       (case values of
                                                           VExp.Value {vexps=vexps,id=id,vType=vType} => ValTable.add(VVar t,vexps,id,vType))
                                                  val () = List.push(LabelInfo.availOut' (getLabelInfo predLabel),VVar t)
                                                  val () = put(predLabel,VVar t)
                                              in
                                                 ()
                                              end
                                          else ()
                                      in
                                          ()
                                      end
                                    val () = case e' of
                                             SOME exp' => 
                                             (case exp' of
                                              VPrimApp {args = args, ...} => insertExp args exp'
                                            | VConApp {args = args, ...} => insertExp args exp'
                                            | VSelect {tuple = tuple,...} => insertExp (Vector.new1 tuple) exp'
                                            | VTuple args => insertExp args exp'
											| VConst _ => insertExp (Vector.new0 ()) exp'
                                            | _  => ()
                                            )
                                           | NONE => ()
                                in
                                ()
                                end)
                    val () = if (!tempValidator) 
                      then 
                          let
                            val t' = Var.newNoname ()
                            val () = List.push(LabelInfo.argsGen' labelInfoObj,(t',v1opv2Type))
                            val _ = nextValNum PartialRedundancy
                            val _ = List.foreach(LabelInfo.predecessor labelInfoObj, fn p =>
                                        let
                                           val predLabel = Block.label p
                                           val pexp = get(predLabel)
                                           
                                        in
                                           case pexp of
                                              NONE => ()
                                            | SOME pexp' =>  
                                                (case pexp' of
                                                    (VVar v) => 
                                                       let 
                                                            val () = List.push(LabelInfo.gotoArgsGen' (getLabelInfo predLabel),v)
                                                                   in
                                                                   ()
                                                                   end
                                                      | _ => ())
                                        end)
                            val () = case ValTable.lookup(v1opv2) of
                                     SOME {values=values',...} => 
                                     (case values' of
                                      VExp.Value {vexps=vexps',id=id',vType=vType'} => ValTable.add(VVar t',vexps',id',vType'))
                                   | NONE => ()
                                   
                            val () = List.push(LabelInfo.availOut' labelInfoObj, VVar t')
                            val () = new_stuff := true          
                            val () = List.push(LabelInfo.newSets' labelInfoObj, VVar t')
                        in
                             ()
                        end
                      else ()
                 in
                    ()
                 end)
               else ()
                
      in
          ()
      end
        
    fun doInsert block new_stuff=
      let
      
          val label = Block.label block
          val labelInfoObj = (getLabelInfo label)
          val () = LabelInfo.newSets' labelInfoObj := []
          val domAvailOut = (case (LabelInfo.dom labelInfoObj) of
                SOME domLabel =>
                let
                val _ = List.foreach(LabelInfo.newSets (getLabelInfo domLabel), fn e =>
                                                   let
                                                       val () = List.push(LabelInfo.newSets' labelInfoObj,e)
                                                       val () = (valReplace (LabelInfo.availOut' (getLabelInfo label)) e)
                                                   in
                                                       ()
                                                   end)
                in
                LabelInfo.availOut (getLabelInfo domLabel)
                end
             |   NONE         => [])
          val () = if (List.length (LabelInfo.predecessor labelInfoObj))>1
               then
               (
                 let
                 val reverseAnticIn = ((LabelInfo.anticIn labelInfoObj))
				 val () = diag "ANTIC_IN worklist inserts "  (Layout.toString (List.layout VExp.layout (reverseAnticIn)))
				 val () = diag "KillGen worklist inserts "  (Layout.toString (List.layout Var.layout (LabelInfo.killGen labelInfoObj)))
                 val worklist = ref reverseAnticIn
				 val () = diagWithLabel label " is merging block"
                 fun doWorkList () =
                   (
                     let
                     val e = List.pop(worklist)
					 val () = diag "inside doworklist " (Layout.toString (VExp.layout e))
                     fun doMergingBlockExp e =
                         (case findLeader(domAvailOut,e) of
                                (*[] => doMergingBlock block e new_stuff 
                            | _   => () *)
							[] => let val () = diag "null exp: " (Layout.toString (VExp.layout e)) in doMergingBlock block e new_stuff end
												| _   => let val () = diag "other exp: " (Layout.toString (VExp.layout e)) in () end)
                     val () = case e of
                               VPrimApp {...} => doMergingBlockExp e
                            |  VConApp {...} => doMergingBlockExp e
                            |  VSelect {...} => doMergingBlockExp e
                            |  VTuple _ => doMergingBlockExp e
							|  VConst _ => doMergingBlockExp e
                            | _ => ()
                     in
                        if (List.length (!worklist))>0
                        then doWorkList ()
                        else ()
                     end
                   )           
                 in
                 if (List.length (!worklist))>0
                 then doWorkList ()
                 else ()
                 end
               )
               else ()
               
      in
          (!new_stuff)
      end
        
    fun insert bfsBlockList =
      let
          val new_stuff = ref false
              val () = new_stuff := (if List.exists((List.map(bfsBlockList, fn block => (doInsert block new_stuff))),fn l => l)
                    then (insert bfsBlockList)
                    else false)
            in
                (!new_stuff)
            end

    fun buildBlock block =
      let
          val args = Block.args block
          val statements = Block.statements block
          val transfer = Block.transfer block
          val label = Block.label block
          val labelInfoObj = (getLabelInfo label)
      in
              let
                  val args' = Vector.fromList (Vector.toList(args)@LabelInfo.argsGen labelInfoObj)
                  val statements' = Vector.fromList (Vector.toList(statements)@List.rev(LabelInfo.statementsGen labelInfoObj))
                  val transfer' = case transfer of
                                   Transfer.Goto {args=gargs,dst=dst} => 
                                       let
                                          val gargs' = Vector.fromList (Vector.toList(gargs)@LabelInfo.gotoArgsGen labelInfoObj)
                                       in
                                          Transfer.Goto {args=gargs',dst=dst}
                                       end
                                   | _ => transfer
              in
                  Block.T {args=args',label=label,transfer=transfer',statements=statements'}
              end
      end
        val globalLabel = Label.fromString "globals"
        val _ = Vector.map(globals, fn s => handleStatements(s, globalLabel))
        val () = globalAvailOut := LabelInfo.availOut (getLabelInfo globalLabel)
        val shrink = shrinkFunction {globals = globals}
        val functions = List.map(functions,fn f =>
                            let
                                val {args, blocks, mayInline, name, raises, returns, start} = Function.dest f
                                val dfsBlockList = ref []
                                val bfsBlockList = ref []
                                val blockTree = (Function.dominatorTree f)
                                val Tree.T (firstBlock, _) = blockTree
                                val firstBlockLabel = Block.label firstBlock
                                val () = Function.dfs(f,fn b => fn () => List.push(dfsBlockList,b))
                                val () = diag "function name" (Func.toString name)
                                val {labelNode=labelNode, nodeBlock=nodeBlock, ...} = Function.controlFlow f
                                val () = handleFunctionArgs args firstBlockLabel
                                val () = loopTree_Phase1 ((Function.dominatorTree f), NONE, labelNode, nodeBlock, bfsBlockList)
                                val _ = doBuildSets_Phase2(!dfsBlockList)
                                val _ = insert(!bfsBlockList)
                                val blocks = Vector.map(blocks, fn b => buildBlock b)
                                val blocks = Vector.map(blocks, fn block => eliminate block)
                            in
                                shrink(shrink(Function.new {args = args,
                                              blocks = blocks,
                                              mayInline = mayInline,
                                              name = name,
                                              raises = raises,
                                              returns = returns,
                                              start = start}
                                       ))
                            end)
        val sCount = nextValNum StatementsAdded
        val pCount = nextValNum PartialRedundancy
        val eCount = nextValNum StatementsEliminated
        val () = diag "statements added: " (Int.toString sCount)
        val () = diag "statements eliminated: " (Int.toString eCount)
        val () = diag "partial redundancies: " (Int.toString pCount)
                          
        val program =
              Program.T {datatypes = datatypes,
                         globals = globals,
                         functions = functions,
                         main = main}

        val _ = Program.clearTop program
    in
        program
  end
end
