functor MkBoruvkaMST (structure Seq : SEQUENCE
                      structure Rand : RANDOM210
                      sharing Seq = Rand.Seq) : MST =
struct
  structure Seq = Rand.Seq
  open Seq

  type vertex = int
  type weight = int
  type edge = vertex * vertex * weight

  (*
  * MST : (edge seq * int) -> edge seq
  *
  * With the given edges of n vertices, MST returns the minimum spanning
  * tree.
  *)
  fun MST (E : edge seq, n : int) : edge seq =
    let
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
        * -> Rand -> (vertex seq * (edge * (vertex * vertex * weight)) seq)
        * returns sequences of contracted vertices and edges.
        *)
        fun minStarContract vSeq eSeq seed =
            let
                val eSeq' = minEdges eSeq
                (* H is a boolean sequence of head and tail *)
                val H = map (fn v => v = 1) (Rand.flip seed n)
                fun tailToHead (u,v,_,_) =(not(nth H u)) andalso (nth H v)
                val eSeq'' = filter tailToHead eSeq'
                (* domain records vertex mapping to contracted vertex *)
                (* eg. <(0,1),(2,3)> => 0->1 and 2->3 *)
                val domain = map (fn (u,v,w,l) => (u,v)) eSeq''
                val vSeq' = inject domain vSeq
            in
                (vSeq', eSeq'')
            end
        (*
        * MST' :
        *    vertex seq -> (edge * (vertex * vertex * weight)) seq
        * -> (vertex * vertex * weight) seq -> Rand
        * -> (vertex * vertex * weight) seq
        * returns minimum spanning tree of the given edges.
        *)
        fun MST' vSeq eSeq labels seed =
            if length eSeq = 0 then labels
            else
                let
                    val (vSeq', eSeq') = minStarContract vSeq eSeq seed
                    val labels' = append((map (fn e => #4e) eSeq'),labels)
                    fun P k = nth vSeq' k
                    val seed' = Rand.next seed
                    val eSeq'' = map (fn (u,v,w,l) => (P u,P v,w,l)) eSeq
                    val eSeq''' = filter (fn (u,v,_,_) => u <> v) eSeq''
                in
                    MST' vSeq' eSeq''' labels' seed'
                end
    in
        MST' V E'' (empty()) r
    end

end
