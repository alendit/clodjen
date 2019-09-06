(ns clodjen.llvm-wrap-test
  (:require [clojure.string :as str]
            [clodjen.llvm-wrap :refer :all]
            [clojure.test :refer :all]))

(defn trim-module [mod]
  (-> mod print-module str/trim-newline))

(defmacro test-func [test-descr fn-name ret-type args blocks test-cases]
  `(testing ~test-descr
    (let [module# (create-module (str ~fn-name "_module"))
          func-ref# (define-function module# ~fn-name ~ret-type ~args ~blocks)]
      (verify-module module#)
      ;; (is (= ~expected-llvm (trim-module module#)))
      (let [engine# (make-execution-engine module#)
            ~'func (fn [& args#] (apply run-function engine# func-ref# args#))]
        ~@test-cases))))

(deftest simple-func
  (test-func "Define and execute a simple function"
             "fac" :i32 [^:i32 input]
             [[:entry [] [eq (cmp input [:i32 1] :eq)
                         res (int-cast eq (types :i32))]
               (ret res)]]
             [(is (= 0 (func 0)))
              (is (= -1 (func 1)))]))

(deftest add-func
  (test-func "Define and execute an adder func"
             "add" :i32 [^:i32 p0 ^:i32 p1]
             [[:entry [] [sum (add p0 p1)]
               (ret sum)]]
             [(is (= 12 (func 6 6)))
              (is (= 24 (func 21 3)))]))

(deftest branching-func
  (test-func "Define and execute a branching func"
             "over21" :i1 [^:i32 score]
             [[:entry []
               [over (cmp score [:i32 21] :gt)]
               (cond-branch over [:then] [:else])]
              [:then [] [] (branch :done [:i1 1])]
              [:else [] [] (branch :done [:i1 0])]
              [:done [^:i1 res] [] (ret res)]]
             [(is (= true (func 22)))
              (is (= false (func 20)))]))

(deftest factorial-func
  (test-func "Define a recursive factorial function"
             "factorial" :i64 [^:i64 x]
             [[:entry
               []
               [break (cmp x [:i64 1] :lt)]
               (cond-branch break [:ret [:i64 1]] [:cont x])]
              [:cont
               [^:i64 y]
               [y-next (sub y [:i64 1])
                res-next (call-func self [y-next])
                res-mul  (mul res-next y)]
               (branch :ret res-mul)]
              [:ret [^:i64 res] [] (ret res)]]
             [(is (= 1 (func 0)))
              (is (= 1 (func 1)))
              (is (= 6 (func 3)))
              (is (= 3628800 (func 10)))]))

(deftest dividing-func
  (test-func "Simple float divider"
             "divide" :d [^:d x ^:d y]
             [[:entry [] [res (fdiv x y)] (ret res)]]
             [(is (= 5. (func 10. 2.)))]))
