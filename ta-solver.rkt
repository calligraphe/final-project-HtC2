;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-advanced-reader.ss" "lang")((modname ta-solver) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #t #t none #f () #f)))


; PROBLEM 1:
; 
; Consider a social network similar to Twitter called Chirper. Each user has a name, a note about
; whether or not they are a verified user, and follows some number of people. 
; 
; Design a data definition for Chirper, including a template that is tail recursive and avoids 
; cycles. 
; 
; Then design a function called most-followers which determines which user in a Chirper Network is 
; followed by the most people.
 

(define-struct user (name note follows))
;; User (make-user String String (listof User))
;; interp. a user w/ name, note whether verified or not, and list of followed users

(define CHIRPER (shared ((-A- (make-user "A" true  (list -B- -C-)))  ;no followwers
                         (-B- (make-user "B" false (list -C-)))      ;followed by A D
                         (-C- (make-user "C" false (list -D-)))      ;followed by A B D
                         (-D- (make-user "D" true  (list -B- -C-)))) ;followed by C
                  -A-))


;; Template: tail recusive, avoids cycles
#;
(define (fn-for-chirper u)
  ;; todo is (listof User) ; worklist acc. ; users to visit
  ;; visited is (listof String) ; context preserving acc. ; keep track of visited users
  (local [(define (fn-for-user u todo visited)
            (if (member (user-name u) visited)   ; (... (user-note u)
                (fn-for-lou todo visited)
                (fn-for-lou (append (user-follows u) todo)
                            (cons (user-name u) visited))))
          
          (define (fn-for-lou todo visited)
            (cond [(empty? todo) (... visited)]
                  [else
                   (fn-for-user (first todo) (rest todo) visited)]))]
    
    (fn-for-user u empty empty)))

;; User -> User
;; produces most followed user
(check-expect (most-followers CHIRPER) (shared ((-A- (make-user "A" true  (list -B- -C-)))  ;no followwers
                                                (-B- (make-user "B" false (list -C-)))      ;followed by A D
                                                (-C- (make-user "C" false (list -D-)))      ;followed by A B D
                                                (-D- (make-user "D" true  (list -B- -C-)))) ;followed by C
                                         -C-))

;(define (most-followers u) (make-user "" false empty))
(define (most-followers u)
  ;; todo is (listof User) ; worklist acc. ; users to visit
  ;; visited is (listof String) ; context preserving acc. ; keep track of visited users
  ;; popular is (listof Fame) ; rsf acc. users w/ nbr. of their followers
  (local [(define-struct fame (u n))
          ;; Fame is (make-fame User Natural)
          ;; interp. user's name and number of followers

          (define (fn-for-user u todo visited popular)
            (if (member (user-name u) visited)   ; (... (user-note u)
                (fn-for-lou todo visited (add-follower u popular)) ; !!! done
                (fn-for-lou (append (user-follows u) todo)
                            (cons (user-name u) visited)
                            (cons (make-fame u 1) popular))))
          
          (define (fn-for-lou todo visited popular)
            (cond [(empty? todo) (most popular)]   ; !!! done
                  [else
                   (fn-for-user (first todo) (rest todo) visited popular)]))

          ;; Helpers:
          ;; User (listof Fame) -> (listof Fame)
          ;; find user and add1
          (define (add-follower u lof)
            ;; rsf ; elts of (listof Fame) seen so far
            (local [(define (add-follower lof rsf)
                      (local [(define one (first lof))]
                        (if (string=? (user-name u)
                                      (user-name (fame-u one)))
                            (cons (make-fame u
                                             (add1 (fame-n one)))
                                  rsf)
                            (add-follower (rest lof) (cons one rsf)))))]
              
              (add-follower lof empty)))

          ;; (listof Fame) -> User
          ;; produce a user with most followers
          (define (most lof)
            ;; rsf is Fame ; w/ greatest fame-n seen so far
            (local [(define (most lof rsf)
                      (cond [(empty? lof) (fame-u rsf)]
                            [else
                             (most (rest lof)
                                   (if (> (fame-n (first lof))
                                          (fame-n rsf))
                                       (first lof)
                                       rsf))]))]
              (most lof (first lof))))]
    
    (fn-for-user u empty empty empty)))


; PROBLEM 2:
; 
; In UBC's version of How to Code, there are often more than 800 students taking 
; the course in any given semester, meaning there are often over 40 Teaching Assistants. 
; 
; Designing a schedule for them by hand is hard work - luckily we've learned enough now to write 
; a program to do it for us! 
; 
; Below are some data definitions for a simplified version of a TA schedule. There are some 
; number of slots that must be filled, each represented by a natural number. Each TA is 
; available for some of these slots, and has a maximum number of shifts they can work. 
; 
; Design a search program that consumes a list of TAs and a list of Slots, and produces one
; valid schedule where each Slot is assigned to a TA, and no TA is working more than their 
; maximum shifts. If no such schedules exist, produce false. 
;
; You should supplement the given check-expects and remember to follow the recipe!


;; Slot is Natural
;; interp. each TA slot has a number, is the same length, and none overlap

(define-struct ta (name max avail))
;; TA is (make-ta String Natural (listof Slot))
;; interp. the TA's name, number of slots they can work, and slots they're available for

(define SOBA (make-ta "Soba" 2 (list 1 3)))
(define UDON (make-ta "Udon" 1 (list 3 4)))
(define RAMEN (make-ta "Ramen" 1 (list 2)))

(define NOODLE-TAs (list SOBA UDON RAMEN))

(define-struct assignment (ta slot))
;; Assignment is (make-assignment TA Slot)
;; interp. the TA is assigned to work the slot

;; Schedule is (listof Assignment)

;; ============================= FUNCTIONS

;; (listof TA) (listof Slot) -> Schedule or false
;; produce valid schedule given TAs and Slots; false if impossible

(check-expect (schedule-tas empty empty) empty)
(check-expect (schedule-tas empty (list 1 2)) false)
(check-expect (schedule-tas (list SOBA) empty) empty)

(check-expect (schedule-tas (list SOBA) (list 1)) (list (make-assignment SOBA 1)))
(check-expect (schedule-tas (list SOBA) (list 2)) false)
(check-expect (schedule-tas (list SOBA) (list 1 3)) (list (make-assignment SOBA 3)
                                                          (make-assignment SOBA 1)))

(check-expect (schedule-tas NOODLE-TAs (list 1 2 3 4)) 
              (list
               (make-assignment UDON 4)
               (make-assignment SOBA 3)
               (make-assignment RAMEN 2)
               (make-assignment SOBA 1)))

(check-expect (schedule-tas NOODLE-TAs (list 1 2 3 4 5)) false)


(define (schedule-tas tas slots)
  (cond [(empty? slots) empty]
        [(slots-avail? tas slots) (solved? (solve (list (make-correct empty tas))
                                                  (first slots)
                                                  tas)        ;here
                                           (rest slots) tas)] ;and here will be untouched tas ;for Schedule
        [else false]))

;; (listof Correct) Slot (listof TA) -> (listof Correct)
;; produce next set of options, or delete existant if impossible
(check-expect (solve (list (make-correct empty NOODLE-TAs)) 3 NOODLE-TAs)
              (list (make-correct (list (make-assignment SOBA 3))
                                  (list (make-ta "Soba" 1 (list 1 3)) UDON RAMEN))
                    (make-correct (list (make-assignment UDON 3))
                                  (list SOBA (make-ta "Udon" 0 (list 3 4)) RAMEN))))

(check-expect (solve (list (make-correct (list (make-assignment SOBA 3))
                                         (list (make-ta "Soba" 1 (list 1 3)) UDON RAMEN))
                           (make-correct (list (make-assignment UDON 3))
                                         (list SOBA (make-ta "Udon" 0 (list 3 4)) RAMEN)))
                     1 NOODLE-TAs)
              
              (list (make-correct (list (make-assignment SOBA 1)
                                        (make-assignment SOBA 3))
                                  (list (make-ta "Soba" 0 (list 1 3)) UDON RAMEN))
                    (make-correct (list (make-assignment SOBA 1)
                                        (make-assignment UDON 3))
                                  (list (make-ta "Soba" 1 (list 1 3)) (make-ta "Udon" 0 (list 3 4)) RAMEN))))


(define (solve loc slot tas0)
  (filter correct?
          (delist
           (map (λ(c)
                  (map (λ(t)
                         (if (and (> (ta-max t) 0) (member slot (ta-avail t)))
                             (make-correct (append (list (make-assignment (get-name t tas0) slot))
                                                   (correct-sch c))
                                           (decrement t (correct-tas c)))
                             false))
                       (correct-tas c)))
                loc))))
; for every correct-tas
;     for every ta
; if respects conditions
;            create loc, appending new Assignment to correct-sch
; if doesn't
;            delete whole Correct


;; (listof (listof X)) -> (listof X)
;; append every elt together
(check-expect (delist empty) empty)
(check-expect (delist (list (list 1 2 3) (list 4 5 6) (list 7 8)))
              (list 1 2 3 4 5 6 7 8))

(define (delist lol0)
  (local [(define (delist lol rsf)
            (cond [(empty? lol) rsf]
                  [else
                   (delist (rest lol)
                           (append rsf (first lol)))]))]
    (delist lol0 empty)))

;; TA (listof TA) -> TA
;; produce given TA from the list
;; ASSUME: func. never reaches empty
(check-expect (get-name (make-ta "Soba" 0 (list 1 3)) NOODLE-TAs)
              SOBA)

(define (get-name t tas)
  (cond [(empty? tas) empty]
        [else
         (if (string=? (ta-name t) (ta-name (first tas)))
             (first tas)
             (get-name t (rest tas)))]))

;; TA (listof TA) -> (listof TA)
;; decrement availability of TA in list by 1
;; ??? ASSUME: (listof TA) is non-empty
(check-expect (decrement (make-ta "Soba" 2 (list 1 3))
                         NOODLE-TAs)
              (list (make-ta "Soba" 1 (list 1 3)) UDON RAMEN))

(define (decrement t tas)
  (cond [(empty? tas) empty]
        [else
         (if (string=? (ta-name t) (ta-name (first tas)))
             (cons (make-ta (ta-name t) (sub1 (ta-max t)) (ta-avail t))
                   (rest tas))
             (cons (first tas) (decrement t (rest tas))))]))

;; (listof Correct) (listof Slot) (listof TA) -> Schedule or false or mutual recursion
;; false if loc is empty, result if los is empty, else call itself w/ next set. 
(check-expect (solved? empty (list 2 3) NOODLE-TAs) false)
(check-expect (solved? (list (make-correct (list (make-assignment SOBA 1))
                                           (list (make-ta "Soba" 1 (list 1 3)) UDON RAMEN)))
                       empty NOODLE-TAs)
              (list (make-assignment SOBA 1)))

(define (solved? loc slots tas0)
  (cond [(empty? loc) false]
        [(empty? slots) (correct-sch (first loc))] ;Schedule
        [else
         (solved? (solve loc (first slots) tas0)
                  (rest slots) tas0)]))

(define-struct correct (sch tas))
;; Correct is (make-correct Schedule (listof TA))
;; interp. next routes to try if current didn't pass
;;         with their own Schedule
;;                    and TAs w/ corrected availability
(define SIMPLE (make-correct (list (make-assignment SOBA 1)
                                   (make-assignment RAMEN 2))
                             (list (make-ta "Soba" 1 (list 1 3))
                                   (make-ta "Ramen" 0 (list 2)))))

;; (listof TA) (listof Slot) -> Boolean
;; true if availability of TAs >= number of slots
;; ASSUME: slots are non-empty
(check-expect (slots-avail? empty (list 1 2)) false)
(check-expect (slots-avail? (list SOBA) (list 1 3)) true)
(check-expect (slots-avail? NOODLE-TAs (list 1 2 3 4)) true)
(check-expect (slots-avail? NOODLE-TAs (list 1 2 3 4 5)) false)

(define (slots-avail? tas slots)
  (<= (length slots)
      (foldr + 0
             (map (λ(ta) (ta-max ta)) tas))))



;; Problem:
(define Erika   (make-ta "Erika"   1 (list 1 3 7 9)))
(define Ryan    (make-ta "Ryan"    1 (list 1 8 10)))
(define Reece   (make-ta "Reece"   1 (list 5 6)))
(define Gordon  (make-ta "Gordon"  2 (list 2 3 9)))
(define David   (make-ta "David"   2 (list 2 8 9)))
(define Katie   (make-ta "Katie"   1 (list 4 6)))
(define Aashish (make-ta "Aashish" 2 (list 1 10)))
(define Grant   (make-ta "Grant"   2 (list 1 11)))
(define Raeanne (make-ta "Raeanne" 2 (list 1 11 12)))

(define Erin    (make-ta "Erin"    1 (list 4)))

(define ALL-tas (list Erika Ryan Reece Gordon David Katie Aashish Grant Raeanne Erin))
(define ALL-slots (list 1 2 3 4 5 6 7 8 9 10 11 12))

;(schedule-tas ALL-tas ALL-slots)