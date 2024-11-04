;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; High level and low level bindings for the IPASIR incremental SAT solver API.

(defpackage #:com.selwynsimsek.sat-lisp
  (:nicknames #:sat-lisp)
  (:use :cl)
  (:shadowing-import-from #:metabang-bind #:bind))
(in-package :sat-lisp)

;;; Libraries

(pushnew '(asdf:system-relative-pathname :sat-lisp #p"lib/")
         cffi:*foreign-library-directories*
         :test #'equal)

;; put more libraries here

(cffi:define-foreign-library picosat
  (:unix (:or "libpicosat.so"))
  (t (:default "libpicosat")))

(cffi:define-foreign-library cadical
  (:unix (:or "libcadical.so"))
  (t (:default "libcadical")))

(cffi:define-foreign-library minisat
  (:unix (:or "libminisat.so"))
  (t (:default "libminisat")))

(defvar *ipasir-library-name* nil)

(defun load-ipasir (&optional (library-name 'cadical))
  (assert (symbolp library-name))
  (when *ipasir-library-name*
    (cffi:close-foreign-library *ipasir-library-name*))
  (cffi:load-foreign-library library-name)
  (setf *ipasir-library-name* library-name))

(defun ensure-ipasir-loaded (&optional (library-name 'cadical))
  (unless (eq *ipasir-library-name* library-name) (load-ipasir library-name)))

(ensure-ipasir-loaded 'cadical)

;;; CFFI bindings

(cffi:defcfun (%ipasir-signature "ipasir_signature") (:pointer :char)
  "Return the name and the version of the incremental SAT solving library.

   IPASIR_API const char * ipasir_signature ();")

(cffi:defcfun (%ipasir-init "ipasir_init") :pointer
  "Construct a new solver and return a pointer to it.

   Required state: N/A
   State after: INPUT

   IPASIR_API void * ipasir_init ();")

(cffi:defcfun (%ipasir-release "ipasir_release") :void
  "Release the solver, i.e., all its resources and allocated memory (destructor).
   The solver pointer cannot be used for any purposes after this call.

   Required state: INPUT or SAT or UNSAT
   State after: undefined

   IPASIR_API void ipasir_release (void * solver);"
  (solver :pointer))


(cffi:defcfun (%ipasir-add "ipasir_add") :void
  "Add the given literal into the currently added clause
   or finalize the clause with a 0.  Clauses added this way
   cannot be removed. The addition of removable clauses
   can be simulated using activation literals and assumptions.

   Required state: INPUT or SAT or UNSAT
   State after: INPUT

   Literals are encoded as (non-zero) integers as in the
   DIMACS formats.  They have to be smaller or equal to
   INT32_MAX and strictly larger than INT32_MIN (to avoid
   negation overflow).  This applies to all the literal
   arguments in API functions.

   IPASIR_API void ipasir_add (void * solver, int32_t lit_or_zero);"
  (solver :pointer) (lit-or-zero :int32))


(cffi:defcfun (%ipasir-assume "ipasir_assume") :void
  "Add an assumption for the next SAT search (the next call
   of ipasir_solve). After calling ipasir_solve all the
   previously added assumptions are cleared.

   Required state: INPUT or SAT or UNSAT
   State after: INPUT

   IPASIR_API void ipasir_assume (void * solver, int32_t lit);"
  (solver :pointer) (lit :int32))

(cffi:defcfun (%ipasir-solve "ipasir_solve") :int
  "Solve the formula with specified clauses under the specified
   assumptions.  If the formula is satisfiable the function returns 10
   and the state of the solver is changed to SAT.  If the formula is
   unsatisfiable the function returns 20 and the state of the solver is
   changed to UNSAT.  If the search is interrupted (see
   ipasir_set_terminate) the function returns 0 and the state of the
   solver is changed to INPUT.  This function can be called in any
   defined state of the solver.  Note that the state of the solver
   _during_ execution of 'ipasir_solve' is undefined.

   Required state: INPUT or SAT or UNSAT
   State after: INPUT or SAT or UNSAT

   IPASIR_API int ipasir_solve (void * solver);"
  (solver :pointer))


(cffi:defcfun (%ipasir-val "ipasir_val") :int32
  "Get the truth value of the given literal in the found satisfying
   assignment.  Return 'lit' if True, '-lit' if False; 'ipasir_val(lit)'
   may return '0' if the found assignment is satisfying for both
   valuations of lit.  Each solution that agrees with all non-zero
   values of ipasir_val() is a model of the formula.

   This function can only be used if ipasir_solve has returned 10
   and no 'ipasir_add' nor 'ipasir_assume' has been called
   since then, i.e., the state of the solver is SAT.

   Required state: SAT
   State after: SAT

   IPASIR_API int32_t ipasir_val (void * solver, int32_t lit);"
  (solver :pointer) (lit :int32))



(cffi:defcfun (%ipasir-failed "ipasir_failed") :int
  "Check if the given assumption literal was used to prove the
   unsatisfiability of the formula under the assumptions
   used for the last SAT search. Return 1 if so, 0 otherwise.

   The formula remains unsatisfiable even just under assumption literals
   for which ipasir_failed() returns 1.  Note that for literals 'lit'
   which are not assumption literals, the behavior of
   'ipasir_failed(lit)' is not specified.

   This function can only be used if ipasir_solve has returned 20 and
   no ipasir_add or ipasir_assume has been called since then, i.e.,
   the state of the solver is UNSAT.

   Required state: UNSAT
   State after: UNSAT

   IPASIR_API int ipasir_failed (void * solver, int32_t lit);"
  (solver :pointer) (lit :int32))


(cffi:defcfun (%ipasir-set-terminate "ipasir_set_terminate") :void
  "Set a callback function used to indicate a termination requirement to
   the solver.  The solver will periodically call this function and
   check its return value during the search.  The ipasir_set_terminate
   function can be called in any state of the solver, the state remains
   unchanged after the call.  The callback function is of the form
   int terminate(void * data)
   - it returns a non-zero value if the solver should terminate.
   - the solver calls the callback function with the parameter data
    having the value passed in the ipasir_set_terminate function
    (2nd parameter).

   Required state: INPUT or SAT or UNSAT
   State after: INPUT or SAT or UNSAT

   IPASIR_API void ipasir_set_terminate (void * solver, void * data, int (*terminate)(void * data));"
  (solver :pointer) (data :pointer) (terminate :pointer))

(cffi:defcallback example-terminate :int ((data :pointer))
  (declare (ignore data))
  0)

(cffi:defcfun (%ipasir-set-learn "ipasir_set_learn") :void
  "Set a callback function used to extract learned clauses up to a given
   length from the solver.  The solver will call this function for each
   learned clause that satisfies the maximum length (literal count)
   condition.  The ipasir_set_learn function can be called in any state
   of the solver, the state remains unchanged after the call.  The
   callback function is of the form
   void learn(void * data, int * clause)
     - the solver calls the callback function with the parameter data
       having the value passed in the ipasir_set_learn function
       (2nd parameter).
     - the argument clause is a pointer to a null terminated integer
       array containing the learned clause. the solver can change the
       data at the memory location that clause points to after the
       function call.
     - the solver calls the callback function from the same thread
       in which ipasir_solve has been called.

   Subsequent calls to ipasir_set_learn override the previously
   set callback function.  Setting the callback function to NULL
   with any max_length argument disables the callback.

   Required state: INPUT or SAT or UNSAT
   State after: INPUT or SAT or UNSAT

   IPASIR_API void ipasir_set_learn (void * solver, void * data, int max_length, void (*learn)(void * data, int32_t * clause));"
  (solver :pointer) (data :pointer) (max-length :int) (learn :pointer))


(cffi:defcallback example-learn :void ((data :pointer) (clause (:pointer :int)))
  (declare (ignore data))
  (let ((data (loop for i from 0
                    until (zerop (cffi:mem-ref clause :int i))
                    collect (cffi:mem-ref clause :int i))))
    (format *error-output* "in example learn: extracting learnt clause~a~%" data)))


(cffi:defcfun (%ipasir-set-seed "ipasir_set_seed") :void (solver :pointer) (seed :int))

(cffi:defcfun (%mallob-ipasir-init "mallob_ipasir_init") :pointer
  "Addition to the interface: enables to create a non-incremental solver which can then be branched
via mallob_ipasir_branched_solve ().

   void* mallob_ipasir_init (bool incremental);"
  (incremental :boolean))

(cffi:defcfun (%mallob-ipasir-branched-solve "mallob_ipasir_branched_solve") :void
  "Addition to the interface: branch off a child solver on the current formulae / assumptions,
   call the provided callback as soon as solving is done. Clears assumptions in the parent solver.

   void mallob_ipasir_branched_solve (void * solver, void * data, int (*terminate)(void * data), void (*callback_done)(int result, void* child_solver, void* data));"
  (solver :pointer) (data :pointer) (terminate :pointer) (callback-done :pointer))

(cffi:defcallback example-callback-done :void ((result :int) (child-solver :pointer) (data :pointer))
  (format *error-output* "in example-callback-done: ~a ~a ~a~%" result child-solver data))

(cffi:defcfun (%mallob-ipasir-presubmit "mallob_ipasir_presubmit") :void
  "Addition to the interface: already begin to introduce the next job to Mallob (via ipasir_solve, not branched_solve!).
   Illegal if the formula transfer mode is not NAMED_PIPE."
  (solver :pointer))

;;; High level API

(defun ipasir-signature () (cffi:foreign-string-to-lisp (%ipasir-signature)))

(defclass incremental-sat-solver ()
  ((solver-pointer :initarg :solver-pointer :accessor solver-pointer :initform nil)
   (symbol-table :initarg :symbol-table :accessor symbol-table :initform (make-hash-table :test 'equalp))
   (variable-count :initarg :variable-count :accessor variable-count :initform 0
                   :documentation "The number of variables so far input to the solver.")
   (added-literals :initarg :added-literals :accessor added-literals
                   :initform (make-array '(0) :element-type 'integer :adjustable t :fill-pointer 0)
                   :documentation "The literals added so far in DIMACS CNF format.")
   (solver-state :initarg :solver-state :accessor solver-state :initform nil
                 :documentation "One of :input, :sat or :unsat."))
  (:documentation "interface to an IPASIR sat solver."))

(defmethod print-object ((object incremental-sat-solver) stream)
  (bind (((:accessors solver-pointer solver-state) object))
        (print-unreadable-object (object stream :type t :identity t)
          (format stream "~a ~a"
                  (when solver-pointer
                    (cffi:pointer-address solver-pointer))
                  solver-state))))

(defmethod initialize-instance :after ((instance incremental-sat-solver)
                                       &rest initargs &key &allow-other-keys)
  (declare (ignore initargs))
  (let ((pointer (%ipasir-init)))
    (setf (solver-pointer instance) pointer
          (solver-state instance) :input)
    (format *debug-io* "Loaded IPASIR SAT solver: ~a~%" (ipasir-signature))))

(defun release-solver (solver)
  (unless (solver-pointer solver)
    (%ipasir-release (solver-pointer solver))
    (setf (solver-pointer solver) nil (solver-state solver) nil)))

(defun add-literal (literal &optional (solver *sat-solver*))
  "Adds a literal to the current clause. Calls %ipasir-add."
  (bind (((:accessors solver-pointer solver-state added-literals) solver))
        (unless (member solver-state (list :sat :unsat :input) :test 'eq)
          (error "invalid solver state for ipasir-add ~a" solver-state))
        (%ipasir-add solver-pointer literal)
        (vector-push-extend literal added-literals)
        (setf (variable-count solver) (max (variable-count solver) (abs literal)))
        (setf solver-state :input)))

(defun add-assumption (literal &optional (solver *sat-solver*))
  (bind (((:accessors solver-pointer solver-state) solver))
        (unless (member solver-state (list :sat :unsat :input) :test 'eq)
          (error "invalid solver state for ipasir-add ~a" solver-state))
        (%ipasir-assume solver-pointer literal)
        (setf solver-state :input)))

(define-condition clause-not-terminated (error)
  ((solver :initarg :solver :accessor solver)))

(define-condition invalid-solver-state (error)
  ((state :initarg :state :accessor state)
   (solver :initarg :solver :accessor solver)))

(defun check-sat (&optional (solver *sat-solver*)) (eq :sat (solve solver)))

(defun solve (&optional (solver *sat-solver*))
  "Tries to solve the solver. Returns one of :sat, :unsat or :input."
  (restart-case
      (bind (((:accessors solver-pointer solver-state added-literals) solver))
        (unless (member solver-state (list :sat :unsat :input) :test 'eq)
          (error 'invalid-solver-state :solver solver :state solver-state))
        (unless (zerop (length added-literals))
          (unless (zerop (aref added-literals (1- (length added-literals))))
            (error 'clause-not-terminated :solver solver)))
        (ecase (%ipasir-solve solver-pointer)
          (0 (setf solver-state :input))
          (10 (setf solver-state :sat))
          (20 (setf solver-state :unsat))))
    (terminate-clause ()
      :report "Terminate the current clause with a zero and try again."
      (add-literal 0 solver)
      (solve solver))))

(defun literal-value (solver literal)
  (restart-case
      (bind (((:accessors solver-pointer solver-state) solver))
        (unless (eq solver-state :sat)
          (error 'invalid-solver-state :state solver-state :solver solver))
        (let ((result (%ipasir-val solver-pointer literal)))
          (if (= result literal)
              t
              (if (= result (- literal))
                  nil
                  (if (zerop result)
                      :indeterminate      ; both true and false assignments are true
                      (error "invalid result ~a" result))))))
    (solve-sat ()
      :report "Try solving the SAT problem and try again."
      (solve solver)
      (literal-value solver literal))))

(defun make-bit-vector (length &optional ones)
  (make-array (list length) :element-type 'bit :initial-element (if ones 1 0)))

(defun model (&optional (solver *sat-solver*))
  (let ((model (make-bit-vector (1+ (variable-count solver)))))
    (loop for i from 1 upto (variable-count solver) do
          (setf (aref model i) (if (literal-value solver i) 1 0)))
    model))

(defun ipasir-failed (solver literal)
  (bind (((:accessors solver-pointer solver-state) solver))
        (unless (eq solver-state :unsat)
          (error 'invalid-solver-state :solver solver :state solver-state))
        (ecase (%ipasir-failed solver literal)
          (0 nil)
          (1 t))))

(defun ipasir-set-terminate (solver terminate-callback &key (data (cffi:null-pointer)))
  (%ipasir-set-terminate (solver-pointer solver) data terminate-callback))

(defun ipasir-set-learn (solver max-length learn-callback &key (data (cffi:null-pointer)))
  (%ipasir-set-learn (solver-pointer solver) data max-length learn-callback))

(defun ipasir-set-seed (solver seed)
  (%ipasir-set-seed (solver-pointer solver) seed))

(defun mallob-ipasir-init (solver boolean)
  (%mallob-ipasir-init (solver-pointer solver) boolean))

(defun mallob-ipasir-branched-solve (solver terminate-callback callback-done-callback
                                     &key (data (cffi:null-pointer)))
  (%mallob-ipasir-branched-solve (solver-pointer solver)
                                 data
                                 terminate-callback
                                 callback-done-callback))

(defun mallob-ipasir-presubmit (solver)
  (%mallob-ipasir-presubmit (solver-pointer solver)))

(defvar *sat-solver* nil)

(defmacro with-sat-solver (&body body)
  `(let ((*sat-solver* (make-instance 'incremental-sat-solver)))
     (unwind-protect (progn ,@body)
       (release-solver *sat-solver*))))

;;; Exports

(export '(picosat
          example-callback-done
          example-learn
          example-terminate
          ipasir-signature
          incremental-sat-solver
          variable-count
          solver-pointer
          *sat-solver*
          symbol-table
          solver-state
          release-solver
          add-literal
          solve
          check-sat
          add-assumption
          clause-not-terminated
          model
          invalid-solver-state
          with-sat-solver
          literal-value))
