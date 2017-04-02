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
val nextValNum =
    let
        val ctr = ref 0
    in
        fn () => (ctr := !ctr + 1 ; !ctr)
    end

val nextValNumIter =
    let
        val ctr = ref 0
    in
        fn () => (ctr := !ctr + 1 ; !ctr)
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
                args: value ref vector,
                            targs: Type.t vector}
           | VVar of Var.t
    and value = Value of {vexps: t list ref, id: int, vType: Type.t}

    fun newValue () = Value {vexps=(ref []), id = nextValNum (), vType = Type.unit}
    fun nullValue () = Value {vexps=(ref []), id = (~1), vType = Type.unit}

    fun valueEquals(xs: value, xs': value) =
        let
            val Value {id=id,...} = xs
            val Value {id=id',...} = xs'
        in
            id=id'
        end

    fun primValueListEquals (xs, xs') = Vector.equals (xs, xs', primValueEquals)
    and primValueEquals(xs: value ref, xs': value ref) = valueEquals(!xs, !xs')
    and equals (e: t, e': t): bool =
    case (e, e') of
            (VConst c, VConst c') => Const.equals (c, c')
          | (VPrimApp {prim, args, ...},
             VPrimApp {prim = prim', args = args',...}) =>
                Prim.equals (prim, prim') andalso primValueListEquals (args, args')
          | (VVar x, VVar x') => Var.equals (x, x')
          | _ => false

    fun layoutValue v =
        let
            open Layout
        in
            case v of
                Value {id=id,vexps=vexps,vType=vType} => seq  [(seq [str "", List.layout layout  (!vexps) ]) , Layout.str (Int.toString id), (Type.layout vType)]
        end

    and layout e =
    let
        open Layout
        fun layoutTuple xs = Vector.layout (fn v => layoutValue (!v)) xs
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
          | VVar x => Var.layout x
    end

    local
        val newHash = Random.word
        val primApp = newHash ()

        fun hasher v =
          let
              val Value {id=id,...} = v
          in
              Word.fromInt id
          end

        fun hashValueList (xs: value ref vector, w: Word.t): Word.t =
            Vector.fold (xs, w, fn (x, w) => Word.xorb (w, hashValue (x,w)))
        and hashValue (xs: value ref, w: Word.t): Word.t =
            Word.xorb (w, hasher (!xs))
    in
        val hash  =
         fn (VConst c) => Const.hash c
          | (VPrimApp {args, ...}) => hashValueList (args, primApp)
          | (VVar x) => Var.hash x
    end

    val hash = hash

end

open Exp Transfer VExp

structure ValTable =
struct
(* Keep a hash table of canonicalized Exps that are in scope. *)
    val table: {hash: word, vexp: VExp.t, values: VExp.value } HashSet.t =
        HashSet.new {hash = #hash}

    fun sort args =
        let
            val ls = Vector.toList args
            fun le (v,v') = case (!v,!v') of
                                ((VExp.Value {id=id,...}), (VExp.Value {id=id',...})) => (id <= id')
        in
            Vector.fromList (List.insertionSort (ls,le))
        end

    fun canon vexp = case vexp of
             VPrimApp {prim=prim,args=args,targs=targs} => if (Prim.isCommutative prim)
                                       then VPrimApp {prim=prim,args = sort args, targs=targs}
                                       else vexp
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
              NONE  => lookupOrAddHelper(ref [vexp], vexp, nextValNum (), ty)
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
                    anticIn = ref []
                   }

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
        val {get = getLabelInfo, ...} =
             Property.get(Label.plist, Property.initFun (fn _ => LabelInfo.new ()))
        fun doNonFunctional(v, label, ty) =
            let
                val () = ValTable.add(VVar v,ref [], nextValNum (), ty)
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

	    fun handleFunctionArgs args blockTree =
	        let
			    val Tree.T (block, children) = blockTree
				val label = Block.label block
				val () = Vector.foreach(args, fn (arg,ty) => let
																val () = ValTable.add(VVar arg,ref [], nextValNum (), ty)
																val () = (valInsert (LabelInfo.availOut' (getLabelInfo label)) (VVar arg))
															 in
															 ()
															 end)
			in
			    ()
			end
        fun handlePhiCondtions(v, label, ty) =
            let
                val () = ValTable.add(VVar v,ref [], nextValNum (), ty)
                val () = List.push(LabelInfo.phiGen' (getLabelInfo label), v)
                val () = (valInsert (LabelInfo.availOut' (getLabelInfo label)) (VVar v))
            in
                ()
            end

        fun handleTransfer _ = ()

        fun handleStatements(s, label) =
        let
            val Statement.T {var=var, exp=exp, ty=ty} = s
            val () =
            (case var of
                 NONE => () (*can there be statements without the RHS part where some things need to be done*)
               | SOME var' =>
               (case exp  of
                       Var v =>
                       (let
                           val (vexps,id) = case (ValTable.lookup (VVar v)) of
                                                SOME {values=value,...} => (case value of
                                                                                Value {vexps=vexps,id=id,...} => (vexps,id))
                                              | NONE => (ref [], nextValNum ())
                           val () = ValTable.add(VVar var', vexps, id, ty)
                           val () = (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VVar v))
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
                                    val valueList = Vector.map(args, fn arg =>
                                                    case (ValTable.lookup (VVar arg)) of
                                                        SOME {values=value,...} => ref value
                                                      | NONE => ref (VExp.newValue ()) (*filler will never happen*))
                                    (*implement the canon exps case here*)
                                    val exp = VPrimApp {args=valueList, prim=prim, targs=targs}
                                    val {values=primValue,...} = ValTable.lookupOrAdd exp ty
                                    val (Value {vexps=values,id=id,...}) = primValue
                                    val () = ValTable.add(VVar var', values, id, ty)
                                    val _ = Vector.map(args, fn arg => (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VVar arg) ))
                                    val () = (valInsert (LabelInfo.expGen' (getLabelInfo label)) (VPrimApp {args=valueList, prim=prim, targs=targs}))
                                    val () = List.push(LabelInfo.tmpGen' (getLabelInfo label), var')
                                in
                                    ()
                                end)
                            else doNonFunctional (var', label, ty)
                       end)
                    | _  => doNonFunctional (var', label, ty) (* what are the other expressions that need to be taken care of *)
                   )
            )
        in
            case var of
                NONE => ()
              | SOME var' => (valInsert (LabelInfo.availOut' (getLabelInfo label)) (VVar var'))
        end

        fun doBuildSets_Phase1 (block) =
            let
                val Block.T {args,label,statements,transfer} = block
                (*val () = diagWithLabel label "do args !!! phi condition"*)
                val _ = Vector.map(args, fn (a, ty) => handlePhiCondtions(a, label, ty))
                (*val () = diagWithLabel label "do statements that is the expressions"*)
                val _ = Vector.map(statements, fn s => handleStatements(s, label))
                (*val () = diagWithLabel label "do the transfer which is empty for now"*)
                val _ = handleTransfer transfer (* filler for now does nothing *)
            in
                ()
            end

        fun loopTree_Phase1 (blockTree, parent, labelNode, nodeBlock, bfsBlockList) =
            let
                val Tree.T (block, children) = blockTree
                val () = List.push(bfsBlockList, block)
                val label = Block.label block
                (*val () = diagWithLabel label "buildset phase 1 started"*)
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
                (*val () = diagWithLabel label "populating the gen lists for the block"*)
                val () = doBuildSets_Phase1 (block)
                (*val () = diagWithLabel label "over with this block"
                val () = diagWithLabel label "lets see the gen list corresponding for this block"
                val () = diagWithLabel label "dom"*)
                (*
                    val dom = case (LabelInfo.dom (getLabelInfo label)) of
                                NONE => "NONE"
                            | SOME dom =>  (Layout.toString (Label.layout dom))
                *)
                (*val () = diagWithLabel label "killOut"*)
                (*val () = diagWithLabel label (Layout.toString (List.layout Var.layout (LabelInfo.killGen (getLabelInfo label))))*)

                (*val () = diagWithLabel label dom
                val () = diagWithLabel label "availOut"
                val () = diagWithLabel label (Layout.toString (List.layout VExp.layout (LabelInfo.availOut (getLabelInfo label))))
                val () = diagWithLabel label "phiGen"
                val () = diagWithLabel label (Layout.toString (List.layout Var.layout (LabelInfo.phiGen (getLabelInfo label))))
                val () = diagWithLabel label "expGen"
                val () = diagWithLabel label (Layout.toString (List.layout VExp.layout (LabelInfo.expGen (getLabelInfo label))))
                val () = diagWithLabel label "tempGem"
                val () = diagWithLabel label (Layout.toString (List.layout Var.layout (LabelInfo.tmpGen (getLabelInfo label))))*)

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
                                              NONE => ref (VExp.newValue ())
                                             |SOME {values,...} => ref values
                                    in
                                        case (!v) of
                                            VExp.Value{id=id,...} => id
                                    end)

                fun allTrue ls = List.exists(ls, fn b => b)

                fun checkValue v = case (!v) of
                           VExp.Value{vexps=vexps,id=id,...} => if List.contains(killToVal,id,Int.equals)
                                                            then false
                                                            else (allTrue (List.map((!vexps), fn vexp => isValid vexp)))

                and isValid vexp = case vexp of
                           (VPrimApp {args=args,...}) => allTrue (Vector.toList (Vector.map(args , fn a => checkValue a)))
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
                                                     | SOME {values = value',...} => if VExp.valueEquals(value, value')
                                                                                      then (
																					       case l of
																						   (VVar var) => [l]
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

        fun someTrue ls = List.forall(ls, fn b => b)

        fun phiTranslate (lst, block, succBlock) =
            let
                (*val () = diag "Phitranslate begins for ANTIC_IN " (Layout.toString (List.layout VExp.layout lst))*)
                val Block.T {transfer,...} = block
                val Block.T {args=fromVar',...} = succBlock
                val toVar' = case transfer of
                         Goto {args,...} => args
                       | _ => 
                         let
                            (*val () = diag "transfer type " (Layout.toString (Transfer.layout transfer))*)
                         in
                            Vector.fromList []
                         end
                fun varToValue v = case (ValTable.lookup (VVar v)) of
                                       NONE => ref (VExp.nullValue ())(*remove this and make -1 case*)
                                     | SOME {values,...} => ref values
                val toVar = Vector.toList toVar'
                val fromVar = List.map(Vector.toList fromVar', fn (arg,_) => arg)
                val toValue = List.map(toVar, fn arg => varToValue arg)
                val fromValue = List.map(fromVar, fn arg => varToValue arg)
                (*val () = diag "fromVar " (Layout.toString (List.layout Var.layout fromVar))*)
                (*val () = diag "toVar " (Layout.toString (List.layout Var.layout toVar))*)
                (*val () = diag "fromValue " (Layout.toString (List.layout (fn v => layoutValue (!v)) fromValue))*)
                (*val () = diag "toValue " (Layout.toString (List.layout (fn v => layoutValue (!v)) toValue))*)
                val {intersect=intersect,...} = (List.set {equals=VExp.primValueEquals, layout=(fn v => layoutValue (!v))})

                fun translate vexp = case vexp of
                             (VVar v) => (case List.index(fromVar, fn v' => Var.equals(v,v')) of
                                      NONE => vexp
                                    | SOME i => (VVar (List.nth(toVar,i)))
                                 )
                           | (VPrimApp {prim=prim, args=args, targs=targs}) =>
                             let
                                 val intersection = intersect (Vector.toList args, fromValue)
                                 fun translateArgs args =
                                    Vector.map(args, fn arg =>
                                      (case List.index(fromValue, fn arg' => VExp.primValueEquals(arg,arg')) of
                                           NONE => arg
                                         | SOME i => (List.nth(toValue,i))
                                      ))
                             in
                                 case intersection of
                                     [] => vexp (* lookup or add *)
                                   | _ => (let
                                              val newVexp = (VPrimApp {prim=prim, args=(translateArgs args), targs=targs})
											  val () =  case ValTable.lookup(vexp) of 
											              NONE => ()
											             |SOME {values,...} => case values of
											                                   VExp.Value{vType=vType,...} => let 
																												val _ = ValTable.lookupOrAdd newVexp vType
																											  in
																											   ()
																											  end
                                           in
                                             newVexp
                                           end)
                             end
                           | x  => x
        in
            case transfer of
                Goto {...} => List.map(lst, translate)
              | _ => []
        end

        fun handleSuccesors (block, childrenCount, children) =
            if childrenCount=1
            then
                let
                    (*val () = diag  "Succesor count for block case 1 " (Int.toString childrenCount)*)
                    val succBlock = List.first children
                    val succBlockLabel = Block.label succBlock
                in
                    phiTranslate (LabelInfo.anticIn (getLabelInfo (succBlockLabel)), block, succBlock)
                end
            else if (childrenCount>1)
            then
                (let
                      (*val () = diag "Succesor count for block case 2 " (Int.toString childrenCount)*)
                      val worklist = ref children
                      val block = List.pop worklist
                      val label = Block.label block
                      val ANTIC_OUT = ref []
                      val () = ANTIC_OUT := LabelInfo.anticIn (getLabelInfo label)
                      (*val () = diag "ANTIC_OUT before removals" (Layout.toString (List.layout VExp.layout (!ANTIC_OUT)))*)
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
                      (*val () = diag "ANTIC_OUT after removals" (Layout.toString (List.layout VExp.layout (!ANTIC_OUT)))*)
                  in
                    (handleWorkList ANTIC_OUT worklist)
                  end)
            else (let
                    (*val () = diag "Succesor count for block case 3 " (Int.toString childrenCount)*)
                 in
                    []
                 end)

        fun loopTree_Phase2 (block) =
            let
                val label = Block.label block
                (*val () = diagWithLabel label "starting with block for this iteration"*)
                val labelInfoObj = (getLabelInfo label)
                val old = (LabelInfo.anticIn labelInfoObj)
                (*val () = diagWithLabel label  (Layout.toString (List.layout VExp.layout old))*)
                val ANTIC_OUT = ref []
                val blockSuccessors = LabelInfo.successor labelInfoObj
                val () = ANTIC_OUT := handleSuccesors (block, List.length blockSuccessors,  blockSuccessors)
                (*val () = diag "ANTIC_OUT "  (Layout.toString (List.layout VExp.layout (!ANTIC_OUT)))*)
                val tmpList = List.map(LabelInfo.tmpGen labelInfoObj, fn v => (VVar v))
                (*val () = diag "tmpList "  (Layout.toString (List.layout VExp.layout tmpList))*)
                val S = diff(!ANTIC_OUT, tmpList)
                (*val () = diag "S "  (Layout.toString (List.layout VExp.layout S))*)
                val () = LabelInfo.anticIn' labelInfoObj := diff(LabelInfo.expGen labelInfoObj, tmpList)
                (*val () = diag "ANTIC_IN "  (Layout.toString (List.layout VExp.layout (LabelInfo.anticIn labelInfoObj)))*)
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
                (*val () = diag "ANTIC_IN After inserts "  (Layout.toString (List.layout VExp.layout (LabelInfo.anticIn (getLabelInfo label))))*)
                val () = LabelInfo.anticIn' (getLabelInfo label) := clean(LabelInfo.anticIn (getLabelInfo label), (LabelInfo.killGen (getLabelInfo label)))
                (*val () = diag "ANTIC_IN After Clean "  (Layout.toString (List.layout VExp.layout (LabelInfo.anticIn (getLabelInfo label))))*)
                (*val () = diagWithLabel label "done with block for this iteration"*)
            in
                if (List.equals(old,(LabelInfo.anticIn (getLabelInfo label)),VExp.equals))
                then false
                else true
            end

        fun doBuildSets_Phase2 (dfsBlockList) =
            let
                val iterNumber = nextValNumIter ()
                (*val () = diag "Starting iteration " (Int.toString iterNumber)*)
                val isChanged = if someTrue(List.map(dfsBlockList, fn block => loopTree_Phase2 block))
                                then doBuildSets_Phase2 (dfsBlockList)
                                else false
                (*val () = diag "Fininshing iteration " (Int.toString iterNumber)*)
            in
                isChanged
            end

        fun eliminateStatements s block =
            let
                val Statement.T {var=var, exp=exp, ty=ty} = s
                val label = Block.label block
                val labelInfoObj = (getLabelInfo label)
            in
                (case var of
                 NONE => s
                   | SOME v => (case exp of
                                    PrimApp {prim=prim,...}=>
                                    (let
                                        (*val () = diag "statement working on " (Layout.toString (Statement.layout s))*)
                                        val exp' =  if (Prim.isFunctional prim)
                                                    then
                                                       (let
                                                           (*val () = diag "availOut" (Layout.toString (List.layout VExp.layout (LabelInfo.availOut labelInfoObj)))*)
                                                           (*val () = diag "exp" (Layout.toString (VExp.layout (VVar v)))*)
                                                           val sList' = findLeader(LabelInfo.availOut labelInfoObj, VVar v)
                                                           (*val () = diag "availOut" (Layout.toString (List.layout VExp.layout sList'))*)


                                                       in
                                                           (case sList' of
                                                            [] => exp
                                                          | [(VVar s')] =>   if VExp.equals(VVar s',VVar v)
                                                                     then exp
                                                                     else (Var s')
                                                          | _ => exp)
                                                       end)
                                                    else exp
                                        (*val () = diag "changed exp " (Layout.toString (Exp.layout exp'))*)
                                    in
                                        Statement.T {var=var, exp=exp', ty=ty}
                                    end)
                                | _ => s)
                )
            end

        fun eliminate block =
            let
                (*val () = diag "eliminate block " (Layout.toString (Block.layout block))*)
                val Block.T {args,label,statements,transfer} = block
                val statements' = Vector.map(statements, fn s => eliminateStatements s block)
                (*val () = diag "" "eliminate done for the block"*)
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
                                                          VExp.Value {vexps=vexps,id=id,vType=vType} => vType)
                                                       | NONE => Type.unit
          fun get(b) = (case List.index(!availKey, fn b' => Label.equals(b,b')) of
                                  NONE => NONE
                                | SOME i => SOME (List.nth(!availValue,i))
                             )
          
          
			fun change(_,_,[]) = []
			|   change(0, v, _::xs) =  v :: xs
			|   change(i, v, x::xs) =  if i < 0 then x::xs
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
									val () = case e' of
											 SOME exp' => 
											 (case exp' of
											  VPrimApp {args=args,targs=targs,prim=prim} =>
											  let
											      fun buildPrimArgs [] = []
												    | buildPrimArgs (l::ls) = 
														let
														    val leaderList = (leader (LabelInfo.availOut (getLabelInfo predLabel)) (!l))
															val () = diag "exp" (Layout.toString (VExp.layoutValue (!l)))
															val () = diag "leader" (Layout.toString (List.layout VExp.layout (leaderList)))
														in
													    case leaderList of
													      [VVar v] => v::(buildPrimArgs ls)
														  | _ => (buildPrimArgs ls)
														end
														  (*[VConst c] => c::(buildPrimArgs ls)
														  | [VPrimApp {args=args,...}] => (buildPrimArgs ls)*)
												  val translatedArgs = Vector.fromList (buildPrimArgs (Vector.toList args))
												  val () = if (Vector.length(translatedArgs)=Vector.length(args))
												           then ()
														   else tempValidator := false
												  val () = if (!tempValidator) 
												  then 
													  let
														  val t = Var.newNoname ()
														  val () = diag "working on: " "adding new 1 statements"
														  val () = diagWithLabel predLabel (Layout.toString (VExp.layout exp'))
														  val newStatement = Statement.T {exp=(PrimApp {args=translatedArgs,targs=targs,prim=prim}),ty=v1opv2Type,var=(SOME t)}
														  val () = diagWithLabel predLabel (Layout.toString (Exp.layout (PrimApp {args=translatedArgs,targs=targs,prim=prim})))
														  val () = diag "statement: " (Layout.toString (Statement.layout newStatement))
														  val () = diag "exp' " (Layout.toString (VExp.layout exp'))
														  val () = diag "v1opv2: " (Layout.toString (VExp.layout v1opv2))
														  val () = List.push(LabelInfo.statementsGen' (getLabelInfo predLabel),newStatement)
														  val () = case (ValTable.lookupOrAdd exp' v1opv2Type) of
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
											| _  => let 
														val () = diagWithLabel predLabel "var i guess"
														val () = diagWithLabel predLabel (Layout.toString (VExp.layout exp')) 
													in 
														() 
													end
											)
											
										   | NONE => let val () = diagWithLabel predLabel " did not match here in some case" in () end
								in
								()
								end)
		   val () =	if (!tempValidator) 
					then
						let
							val t' = Var.newNoname ()
							val () = List.push(LabelInfo.argsGen' labelInfoObj,(t',v1opv2Type))
							val _ = List.foreach(LabelInfo.predecessor labelInfoObj, fn p =>
																		let
																		   val predLabel = Block.label p
																		   val pexp = get(predLabel)
																		   
																		in
																		   case pexp of
																			  NONE => ()
																			| SOME pexp' =>  (case pexp' of
																							   (VVar v) => List.push(LabelInfo.gotoArgsGen' (getLabelInfo predLabel),v)
																							  | _ => ())
																		end)
							val () = case ValTable.lookup(v1opv2) of
									 SOME {values=values',...} => 
									 (case values' of
									  VExp.Value {vexps=vexps',id=id',vType=vType'} => ValTable.add(VVar t',vexps',id',vType'))
								   | NONE => ()
								   
							val () = List.push(LabelInfo.availOut' labelInfoObj, VVar t')
							(*add phi*)
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
				 val reverseAnticIn = (List.rev (LabelInfo.anticIn labelInfoObj))
				 val () = diag "ANTIC_IN worklist inserts "  (Layout.toString (List.layout VExp.layout (reverseAnticIn)))
                 val worklist = ref reverseAnticIn
				 val () = diagWithLabel label " is merging block"
                 fun doWorkList () =
                   (
                     let
                     val e = List.pop(worklist)
                     val () = diag "inside doworklist " (Layout.toString (VExp.layout e))
					 val () = case e of
                                VPrimApp {...} => (case findLeader(domAvailOut,e) of
													[] => let val () = diag "null exp: " (Layout.toString (VExp.layout e)) in doMergingBlock block e new_stuff end
												| _   => let val () = diag "other exp: " (Layout.toString (VExp.layout e)) in () end)
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
              val () = new_stuff := (if someTrue(List.map(bfsBlockList, fn block => (doInsert block new_stuff)))
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
		  if List.length(LabelInfo.argsGen labelInfoObj)>0
		  then
			  let
				val args' = Vector.fromList (Vector.toList(args)@LabelInfo.argsGen labelInfoObj)
			  in
				Block.T {args=args',label=label,transfer=transfer,statements=statements}
			  end
		  else
			  let
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
				  Block.T {args=args,label=label,transfer=transfer',statements=statements'}
			  end
      end

        val globalLabel = Label.fromString "globals"
        (*val () = diag "Number of globals" (Int.toString (Vector.length globals))*)
        (*val () = diag "globals" (Layout.toString (Vector.layout Statement.layout globals))*)
        val _ = Vector.map(globals, fn s => handleStatements(s, globalLabel))

        val functions = List.map(functions,fn f =>
                            let
                                val {args, blocks, mayInline, name, raises, returns, start} = Function.dest f
                                val dfsBlockList = ref []
                                val bfsBlockList = ref []
                                
								val () = Function.dfs(f,fn b => fn () => List.push(dfsBlockList,b))
                                val () = diag "function name" (Func.toString name)
								(*val () = diag "starting buildsets phase 1" "List.map(functions)"*)
								val {labelNode=labelNode, nodeBlock=nodeBlock, ...} = Function.controlFlow f
                                val () = handleFunctionArgs args (Function.dominatorTree f)
								val () = loopTree_Phase1 ((Function.dominatorTree f), NONE, labelNode, nodeBlock, bfsBlockList)
                                (*val () = diag "done with buildsets phase 1" "List.map(functions)"*)
                                (*val () = diag "dfs for function blocks " (Layout.toString (List.layout Block.layout (!dfsBlockList)))*)
                                (*val () = diag "done with buildsets phase 1" "List.map(functions)"*)
                                (*val () = prettyPrinter ()*)
                                (*val () = diag "starting buildsets phase 2" "List.map(functions)"*)
                                val _ = doBuildSets_Phase2(!dfsBlockList)
                                (*val () = diag "done with buildsets phase 2" "List.map(functions)"*)
                                val _ = insert(!bfsBlockList)
                                val blocks = Vector.map(blocks, fn b => buildBlock b)
								
                                val blocks = Vector.map(blocks, fn block => eliminate block)
								
                            in
                                Function.new {args = args,
                                              blocks = blocks,
                                              mayInline = mayInline,
                                              name = name,
                                              raises = raises,
                                              returns = returns,
                                              start = start}
                            end)
        (*val _ = HashSet.foreach (ValTable.table,
                        fn {vexp=vexp, values=values,...} =>
                          let
                              val () = diag "Table" (Layout.toString (Layout.seq [VExp.layout vexp, VExp.layoutValue values]))
                          in
                              ()
                          end)*)
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
