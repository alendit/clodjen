;; This is a clojure wrapper for LLVM SSA IR generation
;; The main entry point is the macro declare-function.
;; The major difference to vanila LLVM IR is the avoidance
;; phi nodes by abstracting basic blocks as kind of functions
;; which can take multiple input parameters. The "call" to the
;; basic blocks happens in the function which can take multiple
;; parameters to pass to the target block.

(ns clodjen.llvm-wrap
  (:require [clodjen.utils :refer [extract-arg-meta]]))

(import '[org.bytedeco.javacpp Pointer PointerPointer BytePointer FunctionPointer])
(import '[org.bytedeco.llvm.LLVM LLVMModuleRef LLVMTypeRef LLVMValueRef
          LLVMExecutionEngineRef LLVMGenericValueRef LLVMBasicBlockRef])
(import '[org.bytedeco.llvm.global LLVM])
(import '[com.sun.jna Function])
(require '[clojure.inspector :as insp])

(require '[clojure.pprint :as pp])

(defn initialize-jit
  "Initialize LLVM jit internals"
  []
  (LLVM/LLVMLinkInMCJIT)
  (LLVM/LLVMInitializeNativeAsmPrinter)
  (LLVM/LLVMInitializeNativeAsmParser)
  (LLVM/LLVMInitializeNativeTarget))

(initialize-jit)

(defn create-module
  "Create a module with name :name"
  [name]
  (LLVM/LLVMModuleCreateWithName name))

;; ## Type definitions
;; Define types
(def types* (let [int-sizes [1 8 16 32 64 128]
                 int-type* #(symbol (str "LLVM/LLVMInt" % "Type"))
                  int-defs      (map (fn [x] [(keyword (str "i" x)) (eval `(~(int-type* x)))]) int-sizes)
                  float-defs {:f (LLVM/LLVMFloatType) :d (LLVM/LLVMDoubleType)}
                  defs (merge int-defs float-defs)]
              (into {} defs)))

(defn throwing-map
  "Wraps the passed map and throws if the requested key doesn't exist"
  [initial-map]
  (fn [name]
    (if-let [t (types* name)]
      t
      (throw (Exception. (str "Unknown type " name))))))

;; Clojure type -> LLVM type ref
(def types (throwing-map [types*]))

;; LLVM type ref -> Clojure type
(def llvm-types (-> types* clojure.set/map-invert throwing-map))

;; Clojure type -> Java Type
(def c-types {:i1  Boolean
              :i8  Byte
              :i16 Short
              :i32 Integer
              :i64 Long
              :f   Float
              :d   Double})

(defn int-type?
  "Is the passed clojure type an integer type?"
  [type]
  (boolean (#{:i1 :i8 :i16 :i32 :i64} type)))

(defn float-type?
  "Is the passed clojure type a floating point type?"
  [type]
  (boolean (#{:d :f} type)))

(defn type-from-meta
  "Reads the metadata of the passed symbol and returns a form which gets
  the matching LLVM type"
  [sym]
  (if-let [sym-meta (meta sym)]
    (let [matched-types (filter sym-meta (keys types*))]
      (case (count matched-types)
        0 (throw (Exception. (str "No type was supplied for the block argument " sym)))
        1 nil
        (throw (Exception. (str "Multiple types supplied for the block argument " sym))))
      `(types ~(first matched-types)))
    (throw (Exception. (str "No type was supplied for the block argument " sym)))))

(defn declare-function
  "Forward declare a function"
  [module fn-name ret-type args]
  `(let [arg-types# ~(vec (map type-from-meta args))
        arg-types-arr# (into-array LLVMTypeRef arg-types#)
        ret-type-llvm# (types ~ret-type)
        func#          (LLVM/LLVMAddFunction ~module ~fn-name (LLVM/LLVMFunctionType ret-type-llvm# (PointerPointer. arg-types-arr#) ~(count args) 0))]
    (LLVM/LLVMSetFunctionCallConv func# LLVM/LLVMCCallConv)
    {:func func# :args ~(vec (map name args)) :args-types arg-types# :ret ~ret-type :name ~fn-name :module ~module}))

;; # Dynamic variable declarations
;; The reference to the current LLVMBuilder object
(declare ^:dynamic builder)
;; The reference to the blocks meta information of form
;; {:block-name {:name :llvm-ref :phis}}
(declare ^:dynamic blocks-map)
;; The reference to the current block meta information
(declare ^:dynamic current-block)

(defn initialize-block
  "Initialize a block and return a map of {:name :llvm :phis}"
  [block]
  `(let [block-llvm# (LLVM/LLVMAppendBasicBlock ~'self ~(name (:name block)))]
    (LLVM/LLVMPositionBuilderAtEnd builder block-llvm#)
    (let [phis# ~(into {} (for [arg (:args block)]
                            `[~(keyword arg) (LLVM/LLVMBuildPhi builder ~(type-from-meta arg) ~(str arg))]))]
      {:name ~(:name block) :llvm block-llvm# :phis phis#})))

(defmacro define-function
  "Main entry point to define a function
  :fn-name function name
  :ret-type clojure type of the return
  :args a vector of type annotated argument names, i.e. [^:i32 x ^:i32 y]
  :bblock list of the basic blocks. Each block has form
          [:block-name [typed-block-inputs] [assignments] (terminator)],
          for example [:cont [^:i32 idx] [next (add idx [:i32 1])] (branch :break idx)]
  "
  [module fn-name ret-type args bblocks]
  (let [block-to-map #(zipmap [:name :args :vars :term] %)
        blocks        (map block-to-map bblocks)
        func-info-sym (gensym)
        block-info-sym (gensym)]
    `(binding [builder (LLVM/LLVMCreateBuilder)]
       (let [~func-info-sym ~(declare-function module fn-name ret-type args)
             ~'self (:func ~func-info-sym)
             ~@(apply concat (map-indexed (fn [index arg] [arg `(get-param ~func-info-sym ~index)]) args))
             ~'blocks-map ~(into {}
                      (for [block blocks]
                        [(:name block) (initialize-block block)]))]
         (binding [blocks-map ~'blocks-map]
           ~@(for [block blocks]
              `(let [block-name#     ~(keyword (:name block))
                     ~block-info-sym (block-name# blocks-map)
                     block-llvm#     (:llvm ~block-info-sym)]
                 (binding [current-block ~block-info-sym]
                   (LLVM/LLVMPositionBuilderAtEnd builder block-llvm#)
                   (let
                       [~@(apply concat (for [arg-name (:args block)]
                                          [(symbol arg-name) `(~(keyword arg-name) (:phis ~block-info-sym))]))
                        ~@(apply concat (for [defs (partition 2 (:vars block))
                                              :let [[name form] defs]]
                                          [name (concat form [(str name)])]))]
                     ~(:term block))))))
         `(LLVM/LLVMDisposeBuilder builder)
         ~func-info-sym))))

(defn const
  "Builds a constant value of given type"
  [type value]
  (let [cl-type (if (instance? LLVMTypeRef type) (c-types type) type)
        llvm-type (types cl-type)]
    (cond
      (int-type? cl-type) (LLVM/LLVMConstInt llvm-type value 1)
      (= (float-type?) cl-type) (LLVM/LLVMConstReal llvm-type value)
      :default (throw (Exception. "Invalid type " type)))))

(defn make-llvm-value
  "Helper function to convert vectors of form [:type :value] to llvm values"
  [arg]
  (cond
    (instance? LLVMValueRef arg)           arg
    (and (seqable? arg) (= 2 (count arg))) (apply const arg)
    :default                               (throw (Exception. (str "Value arg " arg " should be either LLVMValueRef or a (type const) tuple")))))


(defn bind-phis
  "Binds phis for the given block from args"
  [block args]
  (doseq [[phi val] (map vector (vals (:phis (block blocks-map))) args)]
    (LLVM/LLVMAddIncoming phi (make-llvm-value val) (:llvm current-block) 1)))


(defn branch
  "Branch to the target block (given by keyword) and pass it the arguments"
  [target args]
  (let [block-info (target blocks-map)]
    (bind-phis target args)
    (LLVM/LLVMBuildBr builder (:llvm block-info))))


(defn cond-branch
  "Conditionally branch to either block 1 or 2 and give them the provided arguments"
  [cond block-1  args-1 block-2 args-2]
  (do
    (bind-phis block-1 args-1)
    (bind-phis block-2 args-2)
    (let [get-block-llvm #(:llvm (% blocks-map))]
      (LLVM/LLVMBuildCondBr builder cond (get-block-llvm block-1) (get-block-llvm block-2)))))


(defmacro defllvm
  "Macro to wrap a llvm function.
  For arguments marked as ^:value assures that it is indeed an LLVM value
  by calling make-llvm-value on them. Also makes the function accept op-name
  argument which can be used to name the llvm ir variables"
  ([fn-name args body] `(defllvm ~fn-name "" ~args ~body))
  ([fn-name doc args body]
   (let [patch-value-sym (gensym)]
     `(defn ~fn-name ~(str doc) [~@args ~'op-name]
        (let [~@(apply concat (for [arg   args
                                    :when (:value (meta arg))]
                                `[~arg (make-llvm-value ~arg)]))]
          ~body)))))

(defn make-phi [type name]
  "Builds a phi node"
  (LLVM/LLVMBuildPhi builder type name))

(defn phi-incoming
  "Binds incoming values to phi"
  [phi values blocks]
  {:pre (= (count values) (count blocks))}
  (let [values-arr (into-array LLVMValueRef values)
        block-arr (into-array LLVMBasicBlockRef blocks)]
    (LLVM/LLVMAddIncoming phi (PointerPointer. values-arr) (PointerPointer. block-arr) (count values))))

(defllvm call-func
  "Calls function with args"
  [func args]
  (let [llvm-args (map make-llvm-value args)
        args-arr (into-array LLVMValueRef llvm-args)]
    (LLVM/LLVMBuildCall builder func (PointerPointer. args-arr) (count args) op-name)))

(defllvm mul
  "Builds multiplication"
  [^:value val1 ^:value val2]
  (LLVM/LLVMBuildMul builder val1 val2 op-name))

(defllvm add
  "Builds addition"
  [^:value val1 ^:value val2]
  (LLVM/LLVMBuildAdd builder val1 val2 op-name))

(defllvm sub
  "Builds subtraction"
  [^:value val1 ^:value val2]
  (LLVM/LLVMBuildSub builder val1 val2 op-name))

(defllvm fdiv
  "Builds float division"
  [^:value val1 ^:value val2]
  (LLVM/LLVMBuildFDiv builder val1 val2 op-name))

(defllvm cmp
  "Builds comparison between two values. op gives the comparison type"
  [^:value val1 ^:value val2 op]
  (let [llvm-op (case op
                  :eq LLVM/LLVMIntEQ
                  :lt LLVM/LLVMIntSLT
                  :le LLVM/LLVMIntSLE
                  :ge LLVM/LLVMIntSGE
                  :gt LLVM/LLVMIntSGT)]
    (LLVM/LLVMBuildICmp builder llvm-op val1 val2 op-name)))

(defllvm int-cast
  "Casts value to the given type"
  [value type] (LLVM/LLVMBuildIntCast builder value type op-name))

(defn ret
  "Build ret instruction"
  ([] (LLVM/LLVMBuildRetVoid builder))
  ([val]
   (let [llvm-val (make-llvm-value val)]
     (LLVM/LLVMBuildRet builder val))))

(defn get-param
  "Returns function param with index idx"
  [func idx] (LLVM/LLVMGetParam (:func func) idx))

(defn get-params
  "Returns a vector with all function params"
  [func]
  (into [] (map #(get-param func %) (range (count (:args func))))))

(defn optimize-module
  "Run selected optimization passes on the module"
  [mod]
  (let [pass (LLVM/LLVMCreatePassManager)]
    (LLVM/LLVMAddConstantMergePass pass)
    (LLVM/LLVMAddInstructionCombiningPass pass)
    (LLVM/LLVMAddPromoteMemoryToRegisterPass pass)
    (LLVM/LLVMAddGVNPass pass)
    (LLVM/LLVMAddCFGSimplificationPass pass)
    (LLVM/LLVMRunPassManager pass mod)
    (LLVM/LLVMDisposePassManager pass)
    mod))

(declare print-module)

(defn verify-module
  "Verify the module and raise an exception on problems"
  [mod]
  (let [error (BytePointer. (cast Pointer nil))]
    (LLVM/LLVMVerifyModule mod LLVM/LLVMPrintMessageAction error)
    (let [error-str (.getString error)]
      (LLVM/LLVMDisposeMessage error)
      (if (not (empty? error-str))
        (throw (Exception. (str "Module verify failed with: " error-str ", in module " (print-module mod))))))))

(defn print-module
  "Return LLVM IR of the module"
  [mod]
  (let [buf (LLVM/LLVMPrintModuleToString mod)
        s (.getString buf)]
    (LLVM/LLVMDisposeMessage buf)
    s))

(defn make-execution-engine
  "Create an execution engine for the module"
  ([mod] (make-execution-engine mod true))
  ([mod verify]
   (do
     (when verify (verify-module mod))
     (let [engine     (LLVMExecutionEngineRef.)
           error      (BytePointer. (cast Pointer nil))
           mod-result (LLVM/LLVMCreateJITCompilerForModule engine mod 2 error)]
       (if (not= mod-result 0)
         (do
           (println (.getString error))
           (LLVM/LLVMDisposeMessage error)
           (System/exit -1))
         engine)))))

(defn dispose-execution-engine [engine]
  "Dispose the execution engine for the module"
  (LLVM/LLVMDisposeExecutionEngine engine))

(defn run-function
  "Execute the given function"
  ([func args]
   (let [mod (:module func)
         engine (make-execution-engine mod)]
     (apply run-function engine func args)))
  ([engine func args]
   {:pre (= (count args) (count (:args func)))}
   (let [{func-llvm :func
          arg-types :args
          ret-type  :ret
          func-name :name
          func-mod  :module} func
         func-addr          (LLVM/LLVMGetFunctionAddress engine func-name)
         native-func        (com.sun.jna.Function/getFunction (com.sun.jna.Pointer. func-addr) 0 "utf8")
         exec-args          (into-array args)
         exec-res           (.invoke native-func (c-types ret-type) exec-args)]
     exec-res)))



;; (def mod (create-module "mod"))
;; (def fac
;;   (define-function mod "fac" :i64 [^:i64 x]
;;     [[:entry
;;       []
;;       [break (cmp x [:i64 1] :lt)]
;;       (cond-branch break [:ret [:i64 1]] [:cont x])]
;;      [:cont
;;       [^:i64 y]
;;       [y-next (sub y [:i64 1])
;;        res-next (call-func self [y-next])
;;        res-mul  (mul res-next y)]
;;       (branch :ret res-mul)]
;;      [:ret [^:i64 res] [] (ret res)]]))

;; (println (print-module mod))

;; (verify-module mod)

;; (def engine (make-execution-engine mod))

;; (run-function engine fac 10)
