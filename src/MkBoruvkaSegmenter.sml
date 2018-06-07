functor MkBoruvkaSegmenter
  (structure Seq : SEQUENCE
   structure Rand : RANDOM210
   sharing Seq = Rand.Seq)
  : SEGMENTER =
struct
  structure Seq = Rand.Seq
  open Seq

  structure R = Rand
  type vertex = int
  type weight = int
  type edge = vertex * vertex * weight

  (*
  * findSegments : (edge seq * int) -> int -> vertex seq
  *
  * According to the given initial credit for each vertex, findSegments
  * returns a partitioned tree (forest) of the given edges of n vertices.
  *
  * skittles.png with 100 initial credits takes ~10 seconds
  * skittles.png with 1000 initial credits takes ~15 seconds
  * skittles.png with 10000 initial credits takes ~25 seconds
  *)
  fun findSegments (E, n) initial_credit =
    let
      (* C records the credits for each vertices *)
      val C = tabulate (fn i => initial_credit) n
      (* E' contains edges with unique labels for each edge defined as *)
      (* (min(v1,v2),max(v1,v2),w) *)
      val E' = map (fn (a,b,w) =>(a,b,w,(Int.min(a,b),Int.max(a,b),w))) E
      val r = Rand.fromInt n
      (* V records the new contracted vertex for each vertex *)
      val V = tabulate (fn i => i) n
      val emptySeq = map (fn (_) => (~1,0,0,(0,0,0))) V
      (* compareW reverses the order as heavier edges are in front *)
      fun compareW ((_,_,w1,_),(_,_,w2,_)) =
        case (Int.compare (w1,w2)) of
              LESS => GREATER
            | GREATER => LESS
            | EQUAL => EQUAL
      val E'' = sort compareW E'
      (* K records the sequences of contracted vertices for each vertex *)
      (* eg. initially: <<0>,<1>,<2>,<3>> *)
      (*     0->1 & 2->1: <<>,<0,1,2>,<>,<3>> *)
      (*     1->3: <<>,<>,<>,<0,1,2,3>> *)
      (* so the final contracted vertex is 3 *)
      val K = map (fn v => singleton v) V
      (*
      * minEdges :
      *    (edge * (vertex * vertex * weight)) seq
      * -> (edge * (vertex * vertex * weight)) seq
      * returns minimum weight edges of each vertex.
      *)
      fun minEdges eSeq =
        let
          fun Vindexed s = map (fn (u,v,w,l) => (u,(u,v,w,l))) s
          val sSeq = (Vindexed eSeq)
        in
          filter (fn (u,_,_,_) => u <> ~1) (inject sSeq emptySeq)
        end
      (*
      * minStarContract :
      *    vertex seq -> (edge * (vertex * vertex * weight)) seq
      * -> Rand -> int seq -> (vertex seq) seq
      * -> (vertex seq * (edge * (vertex * vertex * weight)) seq *
      *    int seq * (vertex seq) seq)
      * returns sequences of contracted vertices and edges.
      *)
      fun minStarContract vSeq eSeq seed cSeq K =
        let
          val eSeq' = minEdges eSeq
          val H = map (fn v => v = 1) (Rand.flip seed n)
          fun tailToHead (u,v,_,_) =(not(nth H u)) andalso (nth H v)
          val eSeq'' = filter tailToHead eSeq'
          (* domain records vertex mapping to contracted vertex *)
          (* eg. <(0,1),(2,3)> => 0->1 and 2->3 *)
          val domain = map (fn (u,v,w,l) => (u,v)) eSeq''
          val vSeq' = inject domain vSeq
          val wSeq = map (fn (u,v,w,l) => (v,(u,w))) eSeq''
          val wSeq' = collect Int.compare wSeq
          fun minC v s =
            reduce Int.min (nth cSeq v) (map (fn(u,w)=>nth cSeq u) s)
          fun sumW s =
            reduce (op+) 0 (map (fn(u,w)=>w) s)
          (* caculates the new credit for the contracted vertices *)
          val cSeq' = map (fn (v,s)=>(v, (minC v s)-(sumW s))) wSeq'
          val cSeq'' = inject cSeq' cSeq
          (* updates the contracted vertices sequence for each vertex *)
          val newV = map (fn(v,s)=>(v,map (fn(u,w)=>nth K u) s)) wSeq'
          val newV' = map (fn(v,s)=>(v,reduce append (nth K v) s)) newV
          val oldV = map (fn(u,v)=>(u,empty())) domain
          val K' = inject (append(oldV, newV')) K
        in
          (vSeq', eSeq'', cSeq'', K')
        end
      (*
      * MST' :
      *    vertex seq -> (edge * (vertex * vertex * weight)) seq
      * -> Rand -> int seq -> (vertex seq) seq
      * -> (vertex seq) seq
      * returns the sequences of contracted vertices for each vertex.
      *)
      fun MST' vSeq eSeq seed cSeq K =
        if length eSeq = 0 then K
        else
          let
            val (vSeq',eSeq',cSeq',K') =
                minStarContract vSeq eSeq seed cSeq K
            fun P k = nth vSeq' k
            val seed' = Rand.next seed
            val eSeq'' = map (fn (u,v,w,l) => (P u,P v,w,l)) eSeq
            val eSeq''' = filter (fn (u,v,_,_) => u <> v) eSeq''
            (* filter edges that result in negative credits next time *)
            fun validEdges (u,v,w,l) =
                (Int.min(nth cSeq' u,nth cSeq' v) - w >= 0)
            val eSeq'''' = filter validEdges eSeq'''
          in
            MST' vSeq' eSeq'''' seed' cSeq' K'
        end
      val contV = MST' V E'' r C K
      (* create each mappings from original vertex to contracted vertex *)
      val newV = flatten (mapIdx (fn(i,s)=> map (fn(v)=>(v,i)) s) contV)
    in
      inject newV V
    end
end
