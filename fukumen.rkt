#lang rosette/safe

; 覆面算 (verbal arithmetic) using rosette

(require racket/match)

; SEND + MORE = MONEY

(define (digits2num-aux digits)
  (match digits
    [(cons x xs) (+ x (* 10 (digits2num-aux xs)))]
    [nil 0]))

(define (digits2num digits)
  (digits2num-aux (reverse digits)))

(define (isdigit x)
  (and (>= x 0) (< x 10)))

(define (same s e n d m o r y)
  (begin
    (assert (and (> s 0) (< s 10)))
    (assert (isdigit e))
    (assert (isdigit n))
    (assert (isdigit d))
    (assert (and (> m 0) (< s 10)))
    (assert (isdigit o))
    (assert (isdigit r))
    (assert (isdigit y))
    (assert (distinct? s e n d m o r y))
    (assert (= (+ (digits2num (list s e n d)) (digits2num (list m o r e)))
               (digits2num (list m o n e y))))
   ))

(define-symbolic s e n d m o r y integer?)
(define sol (solve (same s e n d m o r y)))

; > sol
; (model
;  [s 9]
;  [e 5]
;  [n 6]
;  [d 7]
;  [m 1]
;  [o 0]
;  [r 8]
;  [y 2])