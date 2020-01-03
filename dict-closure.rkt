#lang racket

;; You can require more modules of your choice.
(require racket/list
         racket/string
         (prefix-in utils: "utils.rkt")
         (prefix-in strat: "strategies.rkt")
         (prefix-in stats: "statistics.rkt")
         (prefix-in swe: "secret-word-enumeration.rkt"))

(provide dictionary-closure
         remove-duplicates)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                  ;;
;; Dictionary Closure                                                               ;;
;; ==================                                                               ;;
;;                                                                                  ;;
;; A choice of substitution can really trigger more substitutions by looking at the ;;
;; partially decrypted text - surely there will be some words which can be uniquely ;;
;; determined using the dictionary. It is prudent to concretize this "choice" as    ;;
;; this purely deterministic (involving absolutely no guess-work). In more          ;;
;; technical terms, this is called "maintaining arc-consistency" (look it up on     ;;
;; Wikipedia).                                                                      ;;
;;                                                                                  ;;
;; This function must utilise the dictionary and the cipher-word-list. Decrypt each ;;
;; word (`utils:decrypt`) and check if the dictionary has:                          ;;
;;                                                                                  ;;
;; 1. a unique completion!                                                          ;;
;;    - Extend your key using the information with this match. Continue exploring   ;;
;;      the words under the extended key.                                           ;;
;; 2. many completions.                                                             ;;
;;    - Do nothing, just continue exploring the words under the same key. If none   ;;
;;      of the words fall into (1), return with the key that you have built so far. ;;
;; 3. no completions!                                                               ;;
;;    - Return `#f` (false), indicating that this partial key is wrong, and we must ;;
;;      revert to the original key.                                                 ;;
;;                                                                                  ;;
;; Returns either of:                                                               ;;
;; a. a (possibly) extended-key.                                                    ;;
;; b. `#f` if this key led to case (3) for some word.                               ;;
;;                                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;REMOVING
(define (removee l e)
  (foldr
   (lambda (x y) (if (equal? e x) y (cons x y)))
   '()
   l))
(define (remove-duplicates l)
  (foldr (lambda (x y) (if (null? y)
                           (list x)
                           (cons x (removee y x))))
         '()
         l))

;USEFUL STRING FNS
(define car-str stats:car-str)
(define cdr-str stats:cdr-str)

;COMPARE WORDS FROM DICT AND YOUR PARTIALLY DECRYPTED ONES
(define (words-match w1 w2 key)
  (cond
    [(words-match-h w1 w2 key) (cond
                                 [(utils:is-monoalphabetic? (remove-duplicates (remove-filled (zip-str w1 w2))) key) #t]
                                 [else #f])]
    [else #f]))

(define (words-match-h w1 w2 key); capitals in dict word-w1 and small in partially decrypted word-w2 
  (cond
    [(not(= (string-length w1) (string-length w2))) #f]
    [(equal? w1 w2) #t]
    [(equal? (car-str w1) (car-str w2)) (words-match-h (cdr-str w1) (cdr-str w2) key)]
    [(char-lower-case? (car-str w2)) (words-match-h (cdr-str w1) (cdr-str w2) key)]
    [else #f]))

;FIND MATCHES FOR WORD (PARTLY DECRYPTED) IN DICT
(define (check word dict matches key);word -partially decrypted from
  (cond
    [(null? dict) (cond
                    [(null? matches) #f]
                    [(null? (cdr matches)) (car matches)]
                    [else 'multiple])]
    [(words-match (car dict) word key) (check word (cdr dict) (cons (car dict) matches) key)]
    [else (check word (cdr dict) matches key)]))

;USEFUL GENERAL FUNCTION
(define (remove-filled l)
  (foldr (lambda (x y)
           (if(char-lower-case? (cdr x))
              (cons x y)
              y))
         '()
         l));removes both capital cases from conses

;WHETHER KEY IS FULL
(define (full-key? key)
  (cond
    [(null? key) #t]
    [(equal? (car key) #\_) #f]
    [else (full-key? (cdr key))]))

;ZIPS STRINGS TO CREATE A SUBSTITUTION
(define (zip-str s1 s2)
  (let
      ([l1 (string->list s1)]
       [l2 (string->list s2)])
    (match (cons l1 l2)
      [(cons '() _) '()]
      [(cons _ '()) '()]
      [(cons (cons a b) (cons c d)) (cons (cons a c) (zip-str (list->string b) (list->string d)))])))

;GEN FNS
(define (all-caps? str)
  (if(= 0 (string-length str))
     #f
     (if(char-upper-case? (stats:car-str str))
        (all-caps? (stats:cdr-str str))
        #t)))
(define (all-in-dict? lst)
  (foldr
   (lambda (x y) (if(swe:in-dict? x) y #f))
   #t
   lst))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;CENTRAL FUNCTIONS
(define (dictionary-closure key)
  (let([input (remove-duplicates (utils:cipher-word-list-f (utils:decrypt key utils:ciphertext)))])
    (dc key input input)))

(define (dc key lst fulllst)
  (cond
    [(full-key? key)
     (cond
       [(all-in-dict? (utils:cipher-word-list-f (utils:decrypt key utils:ciphertext))) #f]
       [else key])]
    [(null? lst) key]
    [else (let
              ([decrypted (check (car lst) utils:dictionary '() key)]
               [newlist (remove (car lst) fulllst)])
            (cond
              [(equal? 'multiple decrypted) (dc key (cdr lst) fulllst)]
              [(equal? #f decrypted) #f]
              [else
       (let*
           ([substitution (remove-filled (zip-str decrypted (car lst)))]
            [newkey (map (lambda(x) (utils:decrypt (utils:add-substitution substitution key) x)) newlist)])
         (dc (utils:add-substitution substitution key)
             (filter all-caps? newkey) (filter all-caps? newkey)))
       ]))]))