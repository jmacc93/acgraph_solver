#lang racket

(require errortrace)

(define (echo x [msg null]) (begin
  (cond [(not (equal? msg null)) (display msg) (display " ")]) ; show message if given
  (displayln x)
  x
))
(define (echo-if c x [msg null]) (begin
  (cond [(not (c x))
    (cond [(not (equal? msg null)) (display msg) (display " ")]) ; show message if given
    (displayln x)
  ])
  x
))

(define (echo/c c)
  (lambda (x) (echo (c (echo x))))
)

(define asserts-on #t)
(define (assert x [msg "Assertion failure"])
  (->  boolean? string?  void?)
  (cond 
    ([not asserts-on] void)
    ([not x] (error msg))
  )
)
(define (assure condfn value [msg "Assertion failure"]) ; assure is like the echo version of assert
  (assert (condfn value) (tostr msg "\nfor" value))
  value
)

(define (listof? guard) (lambda (lst) (and 
  (list? lst)
  (for/and ([elem lst]) (guard elem))
) ))

(define (vectorof? c) (lambda (vec) (and 
  (vector? vec)
  (for/and ([elem vec]) (c elem))
) ))

; Given vec with element i removed
(define (vector-without vec i) (-> (and/c vector? (not/c vector-empty?)) integer?  any/c)
  (for/vector ([j (in-range (vector-length vec))]  #:when (not (equal? i j)))
    (vector-ref vec j)
  )
)

(define (extreme-in lst val-fn extr-fn)
  (define-values (more? get) (sequence-generate lst))
  (if (more?)
    (begin (let* ([maxelem (get)] [maxval (val-fn maxelem)] [maxi 0] [i 1])
      (do () ((not (more?))) (let* ([elem (get)] [value (val-fn elem)])
        (cond [(extr-fn value maxval)
          (set! maxelem elem)
          (set! maxval value)
          (set! maxi i)
        ])
        (set! i (+ i 1))
      ))
      (list maxelem maxval maxi)
    ))
    ; else no elements in lst
    (list null null null)
  )
)
(define (max-in lst fn) (extreme-in lst fn >))
(define (min-in lst fn) (extreme-in lst fn <))

(define-syntax-rule (max-of (x seq) body ...) (max-in seq (lambda (x) body ...)) )
(define-syntax-rule (min-of (x seq) body ...) (min-in seq (lambda (x) body ...)) )

(define (append-one lst elem) (append lst (list elem)))


(define-syntax-rule (matches? value pat)
  (match value [pat #t] [_ #f])
)


(define-syntax-rule (with value pat body ...)
  (match value [pat body ...] [_ void])
)

(define (member? lst value)
  (equal? (member value lst) #f)
)

(define (append-if-not-present lst value)
  (if (member? lst value)
    (append lst (list value))
    lst
  )
)

(define-syntax-rule (hash-set-append! ht key value)
  (hash-set! ht key
    (append-if-not-present (hash-ref ht key '())
      value
    )
  )
)

(define-syntax-rule (for/hash/append (x lst) body ...)
  (let ([ht (make-hash)] [fn (lambda (x) body ...)])
    (for ([y lst]) (let-values ([(key value) (fn y)])
      (hash-set-append! ht key value)
    ))
    ht
  )
)


(define (tostr . args) (apply string-append
  (for/list ([(x i) (in-indexed args)]) 
    (format (if (< (+ i 1) (length args)) "~a " "~a") x)
  )
))

(define (is-nonempty? seq) (let-values ([(more? get) (sequence-generate seq)])
  (more?)
))

(define-syntax-rule (until-false body ...)
  (let loop ()
    (if (begin body ...)
      (loop)
      #f
    )
  )
)

(define (vector-first vec) (-> (and/c vector? (not/c vector-empty?))  any/c)
  (vector-ref vec 0)
)

(define (vector-filter-equal seq fn val)
  (vector-filter 
    (lambda (x) (equal? (fn x) val))
    seq
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; graph and graph-types

;;;; graph

(struct node (type value) #:mutable #:transparent)
(define (node-proper? n) (-> node? boolean?)
  (string? (node-type n))
  ; node-value can be anything
)

(struct edge (type fromi toi) #:mutable #:transparent)
(define (edge-proper? e) (matches? e
  (edge
    (? string? type)
    (? integer? fromi)
    (? integer? toi)
  )
))

(struct graph (nodes edges) #:mutable #:transparent)
(define (graph-proper? gr)  (matches? gr (graph 
  (? (listof? node-proper?) nodes)
  (? (listof? edge-proper?) edges)
)))


;;;;  graph types (graph template information)

(struct graph-types (ntypes etypes) #:mutable #:transparent)

(define (ntypes-proper? ntypes) (-> hash? boolean?) (and
  (for/and ([(name values) ntypes])  (string? name)  ) ; every name is a string
))

(define (etypes-proper? etypes) (-> hash? boolean?) (and
  (for/and ([(names con) etypes]) (and
    (matches? names (list
      (? string? edge-name)
      (? string? from-type-name)
      (? string? to-type-name)
    ))
    (constraint? con)
  )) ; every name is a string
))

(define (graph-types-proper? grtypes) (matches? grtypes
  (graph-types (? ntypes-proper? _node-types) (? etypes-proper? _edge-types))
))

;;;; make a graph-types for a graph:

; default constraint maker
; makes constraint `(con a b)` from epvals which relatively efficiently determines whether `(a b)` is in epvals
(define (default-con-maker epvals)
  ; epvals is like (list from-value to-value) -- endpoint values
  ; first construct a hashtable to speed up searching for whether a given constraint pair appears in epvals
  (define epvals-ht (for/hash/append (ft epvals)  (values ft #t)  ))
  ; from-ht now like: (hash  [1 3] #t  [5 2] #t  ...)
  ; now construct the constraint: given values must appear in epvals
  (lambda (from to)
    (hash-has-key? epvals-ht (list from to))
  )
)

(define (graph-to-graph-types gr [con-maker default-con-maker]) (with gr (graph nodes edges)
  (assure graph-types-proper? (graph-types
    ; ntypes is a hash table from the node types to a list of all unique values
    (for/hash/append (n nodes) (with n (node type value) (values type value)))
    ; etypes is a hash table from edge types (edge type, from type, to type) to constraint functions
    (hash-map/copy
      ; first make a hash table for edge types to endpoint values
      (for/hash/append (e edges) (with e (edge type fromi toi)
        (define from-node (list-ref nodes fromi))
        (define to-node   (list-ref nodes toi))
        (values 
          ; key is all associated types
          (list type (node-type from-node) (node-type to-node)) 
          ; value is endpoint values
          (list (node-value from-node) (node-value to-node))
        )
      ))
      ; then turn all the endpoint values into constraints
      (lambda (types epvals) (values types (con-maker epvals)) )
    )
  ))
))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; acgraph -- alt-constraint graph


; an altnode is a (node . .) with a (node-value .) of alternates
(define (altnode-proper? altnode) (matches? altnode (node
  (? string? _name)
  (? (and/c vector? is-nonempty?) _values)
)))
(define (assure-altnodes-proper altnodes)
  (assert (vector? altnodes) "Must be a vector")
  (for ([anode altnodes]) (with anode (node type vals)
    (assert (string? type) "Must have a string type")
    (assert (vector? vals) "Must have a vector of alternate values")
    (assert (is-nonempty? vals) "Must have at least one alternate value")
  ))
)

(define (constraint? c) (and (procedure? c) (equal? (procedure-arity c) 2) ))

; a constrained edge ; this is what distinguishes a regular graph and an acgraph
(struct conedge (type fromi toi con) #:mutable #:transparent)
( define (conedge-proper? edge) (matches? edge (conedge
  (? string? _type)
  (? integer? _fromi)
  (? integer? _toi)
  (? constraint? _con)
)))

; a graph of alts (possible states for a given node) and constraint edges
(struct acgraph (altnodes conedges) #:mutable #:transparent)
(define (acgraph-proper? gr) (matches? gr (acgraph 
  (? (vectorof? altnode-proper?) _altnodes)
  (? (vectorof? conedge-proper?) _conedges)
)))
(define (assure-acgraph-proper acg) (begin
  (assert acgraph? acg)
  (with acg (acgraph altnodes conedges) 
    (assure-altnodes-proper altnodes)
    (assert ((vectorof? conedge-proper?) conedges))
  )
  acg
))

; convert a graph to a fully unconstrained acgraph
(define (graph-to-acgraph-blank gr grtypes) (-> graph-proper? graph-types-proper?   acgraph-proper?)
  (assure-acgraph-proper (acgraph
    ; a blank acgraph's nodes' values are lists of possible values
    (for/vector ([n (graph-nodes gr)]) (with n (node type _value)
      (node  type  (list->vector (hash-ref (graph-types-ntypes grtypes) type (list)))  )
    ))
    ; a blank acgraph's edges are the same as the original graph's edges, with constraints added
    (for/vector ([e (graph-edges gr)]) (with e (edge type fromi toi)
      (conedge type fromi toi
        ; look up constraint:
        (hash-ref (graph-types-etypes grtypes) (list
          type
          (node-type (list-ref (graph-nodes gr) fromi))
          (node-type (list-ref (graph-nodes gr) toi))
        ))
      )
    ))
  ))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; object <-> graphs conversion

(define (list-to-graph lst)
  (define nodes '())
  (define edges '())
  (for ([i (in-range (length lst))])
    (set! nodes (append-one nodes (node "el" (list-ref lst i)) ) )
    ; previous -> this
    (cond [(> i 0) ; we have a prev element
      (set! edges (append-one edges (edge "prev" i (- i 1)) ) ) ; i-1 -> i
    ])
    ; this -> next
    (cond [(< (+ i 1) (length lst)) ; we have a next element
      (set! edges (append-one edges (edge "next" i (+ i 1)) ) ) ; i -> i+1
    ])
  )
  (assure graph-proper? (graph nodes edges))
)


(define (each-edge-to conedges to-node-i) (vector-filter-equal conedges conedge-toi to-node-i) )
(define (each-edge-from conedges to-node-i) (vector-filter-equal conedges conedge-fromi to-node-i) )


(define (each-node-to conedges nodei edge-type)
  (-> acgraph? integer? string?  (listof? integer?))
  (for/list 
    ([cedge
      (vector-filter-equal conedges conedge-toi nodei
    )] #:when (equal? (conedge-type cedge) edge-type))
    (conedge-fromi cedge)
  )
)
(define (each-node-from conedges nodei edge-type) (-> acgraph? integer? string?  (listof? integer?))
  (for/list 
    ([cedge
      (vector-filter-equal conedges conedge-fromi nodei)
    ] #:when (equal? (conedge-type cedge) edge-type))
    (conedge-toi cedge)
  )
)

(define (last-node-along conedges start-i edge-type)
  (define cur-last-i start-i)
  (let loop () 
    (define next-nodes (each-node-from conedges cur-last-i edge-type))
    (if (empty? next-nodes)
      cur-last-i ; we're done (we found the last node already)
      (begin ; else, we have a new last node
        (set! cur-last-i (first next-nodes) )
        (loop) ; go again
      )
    )
  )
)

(define (each-node-along conedges start-i edge-type)
  (define cur-last-i start-i)
  (define collected-nodes (list))
  (let loop ()
    (set! collected-nodes (append-one collected-nodes cur-last-i))
    (define next-nodes (each-node-from conedges cur-last-i edge-type))
    (if (equal? (length next-nodes) 0)
      collected-nodes ; we're done (we found the last node already)
      (begin ; else, we have a new last node
        (set! cur-last-i (first next-nodes) )
        (loop) ; go again
      )
    )
  )
)

(define (list-acgraph-to-list acg) (-> acgraph? (listof? any/c)) (with acg (acgraph altnodes conedges)
  (if (equal? (vector-length altnodes) 0)
    ; its an empty list
    (list)
    ; else, it's not empty:
    ; collect all the nodes folowing the first node and select only the first alt from each
    (for/list ([i (each-node-along conedges (last-node-along conedges 0 "prev") "next")])
      (vector-first (node-value (vector-ref altnodes i)))
    )
  )
))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; constraint propagation

; is (con a b) satisfied for all a in alst?
(define (con-sat-forall-a?  con alst b) (-> constraint? list? any/c  boolean?)
  (for/and ([a alst])
    (con a b)
  )
)

; is (con a b) satisfied for some a in alst?
(define (con-sat-exists-a?  con alst b) (-> constraint? list? any/c  boolean?)
  (for/or ([a alst])
    (con a b)
  )
)
; is (con a b) satisfied for some a in alst and for all b in blst?
(define (con-sat-exists-a-forall-b?  con alst blst) (-> constraint? list? any/c  boolean?)
  (for/and ([b blst]) (for/or ([a alst])
    (con a b)
  ))
)

; is (con a b) satisfied for all alst
(define (con-sat-forall? con alst blst) (-> constraint? list? list?  boolean?)
  (for/and ([a alst] [b blst])
    (con a b)
  )
)

; is (con a b) satisfied for at least one (a, b) pair from alst * blst
(define (con-sat-exists? con alst blst) (-> constraint? list? list?  boolean?)
  (for/or ([a alst] [b blst])
    (con a b)
  )
)

; select only b values that satisfy the edge constraint
(define (only-b-sat-exists-a con alst blst) (-> constraint? list? list?  boolean?)
  (vector-filter
    (lambda (b) (con-sat-exists-a? con alst b)) 
    blst
  )
)

; remove all alt values that don't satisfy the edge constraint from the given graph
(define (propagate-constraints! acg)
  (-> acgraph?  acgraph?)
  ; we repeatedly remove alt values across the whole acgraph that don't satisfy the edge constraint
  (until-false (with acg (acgraph altnodes conedges) (let ([did-change #f])
    (assert (for/and ([anode altnodes]) (> (vector-length (node-value anode)) 0)) "Constraint propagation")
    (for ([cedge conedges]) ; for each edge
      (define a-node (vector-ref altnodes (conedge-fromi cedge)))
      (define b-node (vector-ref altnodes (conedge-toi cedge)))
      ; only keep b values that satisfy the cedge constraint
      (define new-b-values (only-b-sat-exists-a (conedge-con cedge) (node-value a-node) (node-value b-node)))
      (cond [(not (equal? (vector-length new-b-values) (vector-length (node-value b-node))))
        (set! did-change #t)
      ])
      (set-node-value! b-node new-b-values)
    )
    did-change
  )))
  (assure-acgraph-proper acg)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; acgraph reduction

(define (nonunitary-altnode? altnode) (with altnode (node type vals)
  (> (vector-length vals) 1)
))
(define (on/c c fn)
  (lambda (x) (c (fn x)))
)

(define (least-constrained-nonunitary-altnode-and-index gr) (-> acgraph?  list?)
  ; (assure (on/c nonunitary-altnode? first)  "Cannot select a unitary node from ")
  (define selection (min-of (anode (acgraph-altnodes gr))
    (let ([n (vector-length (node-value anode))])
      (if (> n 1) n  10000) ; only select nodes with more than one alt
    )
  ))
  (if ((on/c nonunitary-altnode? first) selection)
    selection ; only if nonunitary
    (list void void void)
  )
)
(define (least-constrained-nonunitary-altnode gr) (-> acgraph?  integer?)
  (first (least-constrained-nonunitary-altnode-and-index gr))
)
(define (least-constrained-nonunitary-altnode-index gr) (-> acgraph?  integer?)
  (last (least-constrained-nonunitary-altnode-and-index gr))
)
(define (least-constrained-nonunitary-altnode-apply-alts! scg fn)
  (-> acgraph? procedure?  boolean?)
  (define anode (least-constrained-nonunitary-altnode scg))
  (if (not (equal? anode void)) ; found a nonuntary altnode?
    (begin ; yes, so apply to it
      (set-node-value! anode (fn (node-value anode)))
      #t
    )
    #f ; no, graph is unitary
  )
)

; remove all but one element from an alts vector
(define (vector-unitize vec) (-> (and/c vector? (not/c vector-empty?))  vector?)
  ; remove all but one random element
  (assert (> (vector-length vec) 1) "cannot unitize a unitary vector")
  (vector (vector-ref vec
    (random 0 (vector-length vec))
  ))
)
(define (acgraph-reduce/unitize! scg) (least-constrained-nonunitary-altnode-apply-alts! scg vector-unitize))

; remove just one element from an alts vector
(define (vector-eliminate alts) (-> (and/c vector? (not/c vector-empty?))  vector?)
  ; remove one random element
  (assert (> (vector-length alts) 1) "cannot eliminate from a unitary vector")
  (vector-without alts
    (random 0 (vector-length alts))
  )
)
(define (acgraph-reduce/eliminate! scg) (least-constrained-nonunitary-altnode-apply-alts! scg vector-eliminate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; main procedure

(define (fully-constrained? acg) (-> acgraph-proper? boolean?) (with acg (acgraph altnodes conedges)
  (for/and ([anode altnodes]) (with anode (node type vals)
    (equal? (vector-length vals) 1)
  ))
))
(define acgraph-unitary? fully-constrained?)

(define (propagate-reduce-until-fully-constrained! acg [reduction-fn! acgraph-reduce/eliminate!])
  (->  acgraph-proper?  acgraph-proper?)
  (let loop ()
    (propagate-constraints! acg)
    (if (reduction-fn! acg) ; only true if it reduced one nonunitary altnode
      (loop)
      (assure-acgraph-proper acg) ; else return
    )
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define tests (list))

(define (add-test-lambda name fn)
  (set! tests (append tests (list (list name fn))))
)

(define-syntax-rule (add-test name body ...)
  (add-test-lambda name (lambda ()
    body
    ...
  ))
)

(define-syntax-rule (add-error-test name body ...)
  (add-test-lambda name (lambda ()
    (define error-produced #f)
    (with-handlers ([exn? (lambda (e) (set! error-produced #t))])
      body
      ...
    )
    (assert error-produced "No error produced")
  ))
)

(define (run-tests)
  (define fail-count 0)
  (define exceptions (list))
  (for ([named-fn tests]) (with named-fn (list name fn)
    (with-handlers 
      ([exn? (lambda (e)
        (set! fail-count (+ fail-count 1))
        (displayln (tostr name " FAILED"))
        (set! exceptions (append exceptions (list e)))
      )])
      
      (fn)
    )
  ))
  (cond [(not (empty? exceptions))
    (begin
      (displayln (tostr fail-count " tests failed"))
      (begin
        (displayln "reraising first exception")
        (raise (first exceptions))
      )
    )
  ])
)

(add-test "positive assert" (assert #t))
; (add-test "negative assert" (assert #f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(add-test "list-to-graph" (list-to-graph '(1 2 3)))

(add-test "graph-to-graph-types" (graph-to-graph-types (list-to-graph '(1 2 3))))


(add-test "graph-to-acgraph-blank"
  (define gr (list-to-graph '(1 2 3)))
  (define grtypes (graph-to-graph-types gr))
  (define acg (graph-to-acgraph-blank gr grtypes))
  (assure-acgraph-proper acg)
)

(add-test "acgraph-reduce/unitize!"
  (define gr (list-to-graph '(1 2 3)))
  (define grtypes (graph-to-graph-types gr))
  (define acg (graph-to-acgraph-blank gr grtypes))
  (acgraph-reduce/unitize! acg)
  (assure-acgraph-proper acg)
)

(add-test "propagate-constraints!"
  (define gr (list-to-graph '(1 2 3)))
  (define grtypes (graph-to-graph-types gr))
  (define acg (graph-to-acgraph-blank gr grtypes))
  (propagate-constraints! acg)
  (assure-acgraph-proper acg)
)

(add-test "propagate-reduce-until-fully-constrained! acgraph-reduce/eliminate!"
  (for ([i (in-range 100)])
    (random-seed i)
    (define gr (list-to-graph '(1 2 3 4 3 2 3 4 5 4 3 2 1)))
    (define grtypes (graph-to-graph-types gr))
    (define acg (graph-to-acgraph-blank gr grtypes))
    (propagate-reduce-until-fully-constrained! acg acgraph-reduce/eliminate!)
    (assure-acgraph-proper acg)
  )
)

(add-test "list-acgraph-to-list"
  (random-seed 0)
  (define gr (list-to-graph '(1 2 3 4 3 2 3 4 5 4 3 2 1)))
  (define grtypes (graph-to-graph-types gr))
  (define acg (graph-to-acgraph-blank gr grtypes))
  (propagate-reduce-until-fully-constrained! acg)
  (assert (equal? (list-acgraph-to-list acg) (list 4 3 4 3 4 5 4 3 2 3 2 1 2))) ; on seed 0
)

(add-test "vector-unitize"
  (random-seed 0)
  (define gr (list-to-graph '(1 2 3 4 3 2 3 4 5 4 3 2 1)))
  (define grtypes (graph-to-graph-types gr))
  (define acg (graph-to-acgraph-blank gr grtypes))
  (propagate-reduce-until-fully-constrained! acg acgraph-reduce/unitize!)
  (assert (equal? (list-acgraph-to-list acg) (list 5 4 5 4 3 2 3 2 3 2 1 2 3))) ; on seed 0
)

(add-test "unitary without reduction"
  (define gr (list-to-graph '(1 2 3)))
  (define grtypes (graph-to-graph-types gr))
  (define acg (graph-to-acgraph-blank gr grtypes))
  (propagate-constraints! acg)
  (assert (equal? (list-acgraph-to-list acg) (list 1 2 3)))
)


(add-error-test "no propagation solution"
  (define gr (list-to-graph '(1 2 3)))
  (define grtypes (graph-to-graph-types gr))
  (define acg (graph-to-acgraph-blank (list-to-graph '(1 2 3 4 5)) grtypes))
  (propagate-constraints! acg)
)

(run-tests)
(displayln "Done")









