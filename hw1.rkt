#lang plai-typed

; Tree def
(define-type Tree
    [leaf (val : number)]
    [node (val : number)
          (left : Tree)
          (right : Tree)])

; sum
(module+ test
  (test (sum (node 5 (leaf 6) (leaf 7)))
        18)
  (test (sum (leaf 2))
        2)
  (test (sum (node 5 (node 5 (leaf 3) (leaf 2)) (node 7 (node 1 (leaf -1) (leaf -2)) (leaf 22))))
        42))

(define (sum [tree : Tree]) : number
  (type-case Tree tree
    [leaf (v) v]
    [node (v l r) (+ v (+ (sum l) (sum r)))]))

; negate
(module+ test
  (test (negate (node 5 (leaf 6) (leaf 7)))
        (node -5 (leaf -6) (leaf -7)))
  (test (negate (leaf 2))
        (leaf -2))
  (test (negate (node 5 (node 5 (leaf 3) (leaf 2)) (node 7 (node 1 (leaf -1) (leaf -2)) (leaf 22))))
        (node -5 (node -5 (leaf -3) (leaf -2)) (node -7 (node -1 (leaf 1) (leaf 2)) (leaf -22)))))

(define (negate [tree : Tree]) : Tree
  (type-case Tree tree
    [leaf (v) (leaf (- 0 v))]
    [node (v l r) (node (- 0 v) (negate l) (negate r))]))

; contains?
(module+ test
  (test (contains? (node 5 (leaf 6) (leaf 7)) 6)
        #t)
  (test (contains? (node 5 (leaf 6) (leaf 7)) 8)
        #f)
  (test (contains? (leaf 2) 2)
        #t)
  (test (contains? (leaf 2) 1)
        #f)
  (test (contains? (node 5 (node 5 (leaf 3) (leaf 2)) (node 7 (node 1 (leaf -1) (leaf -2)) (leaf 22))) -1)
        #t)
  (test (contains? (node 5 (node 5 (leaf 3) (leaf 2)) (node 7 (node 1 (leaf -1) (leaf -2)) (leaf 22))) 6)
        #f))

(define (contains? [tree : Tree] [n : number]) : boolean
  (type-case Tree tree
    [leaf (v) (eq? v n)]
    [node (v l r) (or (eq? v n)
                      (contains? l n)
                      (contains? r n))]))

; big-leaves?
(module+ test
  (test (big-leaves? (node 5 (leaf 6) (leaf 7)))
        #t)
  (test (big-leaves? (node 5 (node 2 (leaf 8) (leaf 6)) (leaf 7)))
        #f)
  (test (big-leaves? (leaf 2))
        #t))

(define (bigger-leaves? [tree : Tree] [n : number]) : boolean
  (type-case Tree tree
    [leaf (v) (> v n)]
    [node (v l r) (and (> v n)
                       (bigger-leaves? l (+ v n))
                       (bigger-leaves? r (+ v n)))]))

(define (big-leaves? [tree : Tree]) : boolean
  (bigger-leaves? tree 0))

; sorted?
(module+ test
  (test (sorted? (node 5 (leaf 6) (leaf 7)))
        #f)
  (test (sorted? (node 6 (leaf 5) (leaf 7)))
        #t)
  (test (sorted? (leaf 2))
        #t)
  (test (sorted? (node 5 (node 5 (leaf 3) (leaf 2)) (node 7 (node 1 (leaf -1) (leaf -2)) (leaf 22))))
        #f)
  (test (sorted? (node 2 (node -1 (leaf -2) (leaf 1)) (node 7 (node 5 (leaf 3) (leaf 5)) (leaf 22))))
        #t)
  (test (sorted? (node 2 (node -1 (leaf -2) (leaf 3)) (node 7 (node 5 (leaf 3) (leaf 9)) (leaf 22))))
        #f))

(define (ordered? [tree : Tree] [min : number] [max : number]) : boolean
  (type-case Tree tree
    [leaf (v) (and (>= v min)
                   (<= v max))]
    [node (v l r) (and (>= v min)
                       (<= v max)
                       (ordered? l min v)
                       (ordered? r v max))]))
                       
(define (sorted? [tree : Tree]) : boolean
  (ordered? tree -inf.0 +inf.0))