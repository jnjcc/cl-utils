#-sbcl
(error "This program only works for SBCL...")

;;;; Standalone application extracted from SLIME & SBCL to provide
;;;;   pretty backtraces for SBCL.
;;;; The interface is (BACKTRACE-WITH-EXTRA-INFO), adapted from
;;;;   Juho Snellman's Weblog:
;;;;   http://jsnell.iki.fi/blog/archive/2007-12-19-pretty-sbcl-backtraces.html


;;; from swank-sbcl.lisp
(defvar *sldb-stack-top*)

(defun find-stack-top ()
  "FIXME: tweaked..."
  (or sb-debug:*stack-top-hint*
      (sb-di:top-frame)))

;;; from swank-backend.lisp
(define-condition sldb-condition (condition)
  ((original-condition
    :initarg :original-condition
    :accessor original-condition))
  (:report (lambda (condition stream)
             (format stream "Condition in debugger code~@[: ~A~]"
                     (original-condition condition))))
  (:documentation "Wrapper for conditions that should not be debugged.

When a condition arises from the internals of the debugger, it is not
desirable to debug it -- we'd risk entering an endless loop trying to
debug the debugger! Instead, such conditions can be reported to the
user without (re)entering the debugger by wrapping them as
`sldb-condition's."))

(defun call-with-debugging-environment (debugger-loop-fn)
  (declare (type function debugger-loop-fn))
  (let ((*sldb-stack-top* (find-stack-top))
        (sb-debug:*stack-top-hint* nil))
    (handler-bind ((sb-di:debug-condition
                    (lambda (condition)
                      (signal 'sldb-condition
                              :original condition))))
      (funcall debugger-loop-fn))))

(defun nth-frame (index)
  (do ((frame *sldb-stack-top* (sb-di:frame-down frame))
       (i index (1- i)))
      ((zerop i) frame)))

(defun compute-backtrace (start end)
  (let ((end (or end most-positive-fixnum)))
    (loop for f = (nth-frame start) then (sb-di:frame-down f)
       for i from start below end
       while f collect f)))


;;; from swank-backend.lisp
(defmacro converting-errors-to-error-location (&body body)
  (let ((gblock (gensym "CONVERTING-ERRORS+")))
    `(block ,gblock
       (handler-bind ((error
                       #'(lambda (e)
                           (return-from ,gblock
                             (make-error-location e)))))
         ,@body))))

(defun call-with-debootstrapping (fun)
  (handler-bind ((sb-int:bootstrap-package-not-found
                  #'sb-int:debootstrap-package))
    (funcall fun)))

(defmacro with-debootstrapping (&body body)
  `(call-with-debootstrapping (lambda () ,@body)))

(defstruct (:location (:type list) :named
                      (:constructor make-location
                                    (buffer position &optional hints)))
  buffer position
  ;; Hints is a property list optionally containing:
  ;;   :snippet SOURCE-TEXT
  ;;     This is a snippet of the actual source text at the start of
  ;;     the definition, which could be used in a text search.
  hints)

(defun make-error-location (datum &rest args)
  (cond ((typep datum 'condition)
         `(:error ,(format nil "Error: ~A" datum)))
        ((symbolp datum)
         `(:error ,(format nil "Error: ~A"
                           (apply #'make-condition datum args))))
        (t
         (assert (stringp datum))
         `(:error ,(apply #'format nil datum args)))))

(defun code-location-has-debug-block-info-p (code-location)
  (handler-case
      (progn (sb-di:code-location-debug-block code-location)
             t)
    (sb-di:no-debug-blocks  () nil)))



;;; from sb-introspect
(defstruct definition-source
  ;; Pathname of the source file that the definition was compiled from.
  ;; This is null if the definition was not compiled from a file.
  (pathname nil :type (or null pathname))
  ;; Source-path of the definition within the file.
  ;; This may be incomplete depending on the debug level at which the
  ;; source was compiled.
  (form-path '() :type list)
  ;; Character offset of the top-level-form containing the definition.
  ;; This corresponds to the first element of form-path.
  (character-offset nil :type (or null integer))
  ;; File-write-date of the source file when compiled.
  ;; Null if not compiled from a file.
  (file-write-date nil :type (or null integer))
  ;; plist from WITH-COMPILATION-UNIT
  (plist nil)
  ;; Any extra metadata that the caller might be interested in. For
  ;; example the specializers of the method whose definition-source this
  ;; is.
  (description nil :type list))

(defun translate-source-location (location)
  (if location
      (make-definition-source
       :pathname (let ((n (sb-c:definition-source-location-namestring location)))
                   (when n
                     (parse-namestring n)))
       :form-path
       (let ((number (sb-c:definition-source-location-toplevel-form-number
                         location)))
         (when number
           (list number)))
       :plist (sb-c:definition-source-location-plist location))
      (make-definition-source)))

(defun vop-sources-from-fun-templates (name)
  (let ((fun-info (sb-int:info :function :info name)))
    (when fun-info
      (loop for vop in (sb-c::fun-info-templates fun-info)
         for source = (find-definition-source
                       (sb-c::vop-info-generator-function vop))
         do (setf (definition-source-description source)
                  (list (sb-c::template-name vop)
                        (sb-c::template-note vop)))
         collect source))))

(defun find-vop-source (name)
  (let* ((templates (vop-sources-from-fun-templates name))
         (vop (gethash name sb-c::*backend-template-names*))
         (source (and vop
                      (find-definition-source
                       (sb-c::vop-info-generator-function vop)))))
    (when source
      (setf (definition-source-description source)
            (list name)))
    (if source
        (cons source templates)
        templates)))

(defun find-definition-sources-by-name (name type)
  (flet ((listify (x)
           (if (listp x)
               x
               (list x)))
         (get-class (name)
           (and (symbolp name)
                (find-class name nil)))
         (real-fdefinition (name)
           ;; for getting the real function object, even if the
           ;; function is being profiled
           (let ((profile-info (gethash name sb-profile::*profiled-fun-name->info*)))
             (if profile-info
                 (sb-profile::profile-info-encapsulated-fun profile-info)
                 (fdefinition name)))))
    (listify
     (case type
       ((:variable)
        (when (and (symbolp name)
                   (eq (sb-int:info :variable :kind name) :special))
          (translate-source-location (sb-int:info :source-location type name))))
       ((:constant)
        (when (and (symbolp name)
                   (eq (sb-int:info :variable :kind name) :constant))
          (translate-source-location (sb-int:info :source-location type name))))
       ((:symbol-macro)
        (when (and (symbolp name)
                   (eq (sb-int:info :variable :kind name) :macro))
          (translate-source-location (sb-int:info :source-location type name))))
       ((:macro)
        (when (and (symbolp name)
                   (macro-function name))
          (find-definition-source (macro-function name))))
       ((:compiler-macro)
        (when (compiler-macro-function name)
          (find-definition-source (compiler-macro-function name))))
       ((:function :generic-function)
        (when (and (fboundp name)
                   (or (not (symbolp name))
                       (not (macro-function name))
                       (special-operator-p name)))
          (let ((fun (real-fdefinition name)))
            (when (eq (not (typep fun 'generic-function))
                      (not (eq type :generic-function)))
              (find-definition-source fun)))))
       ((:type)
        ;; Source locations for types are saved separately when the expander
        ;; is a closure without a good source-location.
        (let ((loc (sb-int:info :type :source-location name)))
          (if loc
              (translate-source-location loc)
              (let ((expander-fun (sb-int:info :type :expander name)))
                (when expander-fun
                  (find-definition-source expander-fun))))))
       ((:method)
        (when (fboundp name)
          (let ((fun (real-fdefinition name)))
            (when (typep fun 'generic-function)
              (loop for method in (sb-mop::generic-function-methods
                                   fun)
                 for source = (find-definition-source method)
                 when source collect source)))))
       ((:setf-expander)
        (when (and (consp name)
                   (eq (car name) 'setf))
          (setf name (cadr name)))
        (let ((expander (or (sb-int:info :setf :inverse name)
                            (sb-int:info :setf :expander name))))
          (when expander
            (find-definition-source (if (symbolp expander)
                                        (symbol-function expander)
                                        expander)))))
       ((:structure)
        (let ((class (get-class name)))
          (if class
              (when (typep class 'sb-pcl::structure-class)
                (find-definition-source class))
              (when (sb-int:info :typed-structure :info name)
                (translate-source-location
                 (sb-int:info :source-location :typed-structure name))))))
       ((:condition :class)
        (let ((class (get-class name)))
          (when (and class
                     (not (typep class 'sb-pcl::structure-class)))
            (when (eq (not (typep class 'sb-pcl::condition-class))
                      (not (eq type :condition)))
              (find-definition-source class)))))
       ((:method-combination)
        (let ((combination-fun
               (find-method #'sb-mop:find-method-combination
                            nil
                            (list (find-class 'generic-function)
                                  (list 'eql name)
                                  t)
                            nil)))
          (when combination-fun
            (find-definition-source combination-fun))))
       ((:package)
        (when (symbolp name)
          (let ((package (find-package name)))
            (when package
              (find-definition-source package)))))
       ;; TRANSFORM and OPTIMIZER handling from swank-sbcl
       ((:transform)
        (when (symbolp name)
          (let ((fun-info (sb-int:info :function :info name)))
            (when fun-info
              (loop for xform in (sb-c::fun-info-transforms fun-info)
                 for source = (find-definition-source
                               (sb-c::transform-function xform))
                 for typespec = (sb-kernel:type-specifier
                                 (sb-c::transform-type xform))
                 for note = (sb-c::transform-note xform)
                 do (setf (definition-source-description source)
                          (if (consp typespec)
                              (list (second typespec) note)
                              (list note)))
                 collect source)))))
       ((:optimizer)
        (let ((fun-info (and (symbolp name)
                             (sb-int:info :function :info name))))
          (when fun-info
            (let ((otypes '((sb-c:fun-info-derive-type . sb-c:derive-type)
                            (sb-c:fun-info-ltn-annotate . sb-c:ltn-annotate)
                            (sb-c:fun-info-optimizer . sb-c:optimizer)
                            (sb-c:fun-info-ir2-convert . sb-c:ir2-convert)
                            (sb-c::fun-info-stack-allocate-result
                             . sb-c::stack-allocate-result))))
              (loop for (reader . name) in otypes
                 for fn = (funcall reader fun-info)
                 when fn collect
                   (let ((source (find-definition-source fn)))
                     (setf (definition-source-description source)
                           (list name))
                     source))))))
       ((:vop)
        (when (symbolp name)
          (find-vop-source name)))
       ((:source-transform)
        (when (symbolp name)
          (let ((transform-fun (sb-int:info :function :source-transform name)))
            (when transform-fun
              (find-definition-source transform-fun)))))
       (t
        nil)))))

(defvar *struct-slotplace-reader*
  (sb-vm::%simple-fun-self #'definition-source-pathname))
(defvar *struct-slotplace-writer*
  (sb-vm::%simple-fun-self #'(setf definition-source-pathname)))
(defvar *struct-predicate*
  (sb-vm::%simple-fun-self #'definition-source-p))
(defvar *struct-copier*
  (sb-vm::%simple-fun-self #'copy-definition-source))
(defun struct-accessor-p (function)
  (let ((self (sb-vm::%simple-fun-self function)))
    ;; FIXME there are other kinds of struct accessor.  Fill out this list
    (member self (list *struct-slotplace-reader*
                       *struct-slotplace-writer*))))

(defun struct-copier-p (function)
  (let ((self (sb-vm::%simple-fun-self function)))
    ;; FIXME there may be other structure copier functions
    (member self (list *struct-copier*))))

(defun struct-predicate-p (function)
  (let ((self (sb-vm::%simple-fun-self function)))
    ;; FIXME there may be other structure predicate functions
    (member self (list *struct-predicate*))))

(defun struct-accessor-structure-class (function)
  (let ((self (sb-vm::%simple-fun-self function)))
    (cond
      ((member self (list *struct-slotplace-reader* *struct-slotplace-writer*))
       (find-class
        (sb-kernel::classoid-name
         (sb-kernel::layout-classoid
          (sb-kernel:%closure-index-ref function 1)))))
      )))

(defun struct-copier-structure-class (function)
  (let ((self (sb-vm::%simple-fun-self function)))
    (cond
      ((member self (list *struct-copier*))
       (find-class
        (sb-kernel::classoid-name
         (sb-kernel::layout-classoid
          (sb-kernel:%closure-index-ref function 0)))))
      )))

(defun struct-predicate-structure-class (function)
  (let ((self (sb-vm::%simple-fun-self function)))
    (cond
      ((member self (list *struct-predicate*))
       (find-class
        (sb-kernel::classoid-name
         (sb-kernel::layout-classoid
          (sb-kernel:%closure-index-ref function 0)))))
      )))

(deftype debug-info ()
  "Structure containing all the debug information related to a function.
Function objects reference debug-infos which in turn reference
debug-sources and so on."
  'sb-c::compiled-debug-info)

(deftype debug-source ()
  "Debug sources describe where to find source code.
For example, the debug source for a function compiled from a file will
include the pathname of the file and the position of the definition."
  'sb-c::debug-source)

(deftype debug-function ()
  "Debug function represent static compile-time information about a function."
  'sb-c::compiled-debug-fun)

(declaim (ftype (function (function) debug-info) function-debug-info))
(defun function-debug-info (function)
  (let* ((function-object (sb-kernel::%fun-fun function))
         (function-header (sb-kernel:fun-code-header function-object)))
    (sb-kernel:%code-debug-info function-header)))

(declaim (ftype (function (debug-info) debug-source) debug-info-source))
(defun debug-info-source (debug-info)
  (sb-c::debug-info-source debug-info))

(declaim (ftype (function (function) debug-source) function-debug-source))
(defun function-debug-source (function)
  (debug-info-source (function-debug-info function)))

(declaim (ftype (function (debug-info) debug-function) debug-info-debug-function))
(defun debug-info-debug-function (debug-info)
  (elt (sb-c::compiled-debug-info-fun-map debug-info) 0))

(defun find-function-definition-source (function)
  (let* ((debug-info (function-debug-info function))
         (debug-source (debug-info-source debug-info))
         (debug-fun (debug-info-debug-function debug-info))
         (tlf (if debug-fun (sb-c::compiled-debug-fun-tlf-number debug-fun))))
    (make-definition-source
     :pathname
     ;; KLUDGE: at the moment, we don't record the correct toplevel
     ;; form number for forms processed by EVAL (including EVAL-WHEN
     ;; :COMPILE-TOPLEVEL).  Until that's fixed, don't return a
     ;; DEFINITION-SOURCE with a pathname.  (When that's fixed, take
     ;; out the (not (debug-source-form ...)) test.
     (when (stringp (sb-c::debug-source-namestring debug-source))
       (parse-namestring (sb-c::debug-source-namestring debug-source)))
     :character-offset
     (if tlf
         (elt (sb-c::debug-source-start-positions debug-source) tlf))
     ;; Unfortunately there is no proper source path available in the
     ;; debug-source. FIXME: We could use sb-di:code-locations to get
     ;; a full source path. -luke (12/Mar/2005)
     :form-path (if tlf (list tlf))
     :file-write-date (sb-c::debug-source-created debug-source)
     :plist (sb-c::debug-source-plist debug-source))))

(defun find-definition-source (object)
  (typecase object
    ((or sb-pcl::condition-class sb-pcl::structure-class)
     (let ((classoid (sb-impl::find-classoid (class-name object))))
       (when classoid
         (let ((layout (sb-impl::classoid-layout classoid)))
           (when layout
             (translate-source-location
              (sb-kernel::layout-source-location layout)))))))
    (method-combination
     (car
      (find-definition-sources-by-name
       (sb-pcl::method-combination-type-name object) :method-combination)))
    (package
     (translate-source-location (sb-impl::package-source-location object)))
    (class
     (translate-source-location (sb-pcl::definition-source object)))
    ;; Use the PCL definition location information instead of the function
    ;; debug-info for methods and generic functions. Sometimes the
    ;; debug-info would point into PCL internals instead of the proper
    ;; location.
    (generic-function
     (let ((source (translate-source-location
                    (sb-pcl::definition-source object))))
       (when source
         (setf (definition-source-description source)
               (list (sb-mop:generic-function-lambda-list object))))
       source))
    (method
     (let ((source (translate-source-location
                    (sb-pcl::definition-source object))))
       (when source
         (setf (definition-source-description source)
               (append (method-qualifiers object)
                       (if (sb-mop:method-generic-function object)
                           (sb-pcl::unparse-specializers
                            (sb-mop:method-generic-function object)
                            (sb-mop:method-specializers object))
                           (sb-mop:method-specializers object)))))
       source))
    #+sb-eval
    (sb-eval:interpreted-function
     (let ((source (translate-source-location
                    (sb-eval:interpreted-function-source-location object))))
       source))
    (function
     (cond ((struct-accessor-p object)
            (find-definition-source
             (struct-accessor-structure-class object)))
           ((struct-predicate-p object)
            (find-definition-source
             (struct-predicate-structure-class object)))
           ((struct-copier-p object)
            (find-definition-source
             (struct-copier-structure-class object)))
           (t
            (find-function-definition-source object))))
    ((or condition standard-object structure-object)
     (find-definition-source (class-of object)))
    (t
     (error "Don't know how to retrieve source location for a ~S"
            (type-of object)))))



;;; from swank-backend.lisp
(defun find-external-format (coding-system)
  (if (equal coding-system "iso-latin-1-unix")
      :default
      nil))
(defun %search-coding (str start end)
  (let ((p (search "coding:" str :start2 start :end2 end)))
    (when p
      (incf p (length "coding:"))
      (loop while (and (< p end)
                       (member (aref str p) '(#\space #\tab)))
         do (incf p))
      (let ((end (position-if (lambda (c) (find c '(#\space #\tab #\newline)))
                              str :start p)))
        (find-external-format (subseq str p end))))))

(defun guess-external-format (pathname)
  "Detect the external format for the file with name pathname.
Return nil if the file contains no special markers."
  ;; Look for a Emacs-style -*- coding: ... -*- or Local Variable: section.
  (with-open-file (s pathname :if-does-not-exist nil
                     :external-format (or (find-external-format "latin-1-unix")
                                          :default))
    (if s
        (or (let* ((line (read-line s nil))
                   (p (search "-*-" line)))
              (when p
                (let* ((start (+ p (length "-*-")))
                       (end (search "-*-" line :start2 start)))
                  (when end
                    (%search-coding line start end)))))
            (let* ((len (file-length s))
                   (buf (make-string (min len 3000))))
              (file-position s (- len (length buf)))
              (read-sequence buf s)
              (let ((start (search "Local Variables:" buf :from-end t))
                    (end (search "End:" buf :from-end t)))
                (and start end (< start end)
                     (%search-coding buf start end))))))))


;;; from swank-source-file-cache.lisp
(defvar *cache-sourcecode* t)
(defvar *source-file-cache* (make-hash-table :test 'equal))
(defstruct (source-cache-entry
             (:conc-name source-cache-entry.)
             (:constructor make-source-cache-entry (text date)))
  text date)

(defun read-file (filename)
  "Return the entire contents of FILENAME as a string."
  (with-open-file (s filename :direction :input
                     :external-format (or (guess-external-format filename)
                                          (find-external-format "latin-1")
                                          :default))
    (let* ((string (make-string (file-length s)))
           (length (read-sequence string s)))
      (subseq string 0 length))))

(defun source-cache-get (filename date)
  "Return the source code for FILENAME as written on DATE in a string.
Return NIL if the right version cannot be found."
  (when *cache-sourcecode*
    (let ((entry (gethash filename *source-file-cache*)))
      (cond ((and entry (equal date (source-cache-entry.date entry)))
             ;; Cache hit.
             (source-cache-entry.text entry))
            ((or (null entry)
                 (not (equal date (source-cache-entry.date entry))))
             ;; Cache miss.
             (if (equal (file-write-date filename) date)
                 ;; File on disk has the correct version.
                 (let ((source (read-file filename)))
                   (setf (gethash filename *source-file-cache*)
                         (make-source-cache-entry source date))
                   source)
                 nil))))))

(defun get-source-code (filename code-date)
  "Return the source code for FILENAME as written on DATE in a string.
If the exact version cannot be found then return the current one from disk."
  (or (source-cache-get filename code-date)
      (read-file filename)))

(defun skip-comments-and-whitespace (stream)
  (case (peek-char nil stream)
    ((#\Space #\Tab #\Newline #\Linefeed #\Page)
     (read-char stream)
     (skip-comments-and-whitespace stream))
    (#\;
     (read-line stream)
     (skip-comments-and-whitespace stream))))

(defun read-upto-n-chars (stream n)
  "Return a string of upto N chars from STREAM."
  (let* ((string (make-string n))
         (chars  (read-sequence string stream)))
    (subseq string 0 chars)))

(defvar *source-snippet-size* 256)
(defun read-snippet (stream &optional position)
  "Read a string of upto *SOURCE-SNIPPET-SIZE* characters from STREAM.
If POSITION is given, set the STREAM's file position first."
  (when position
    (file-position stream position))
  (skip-comments-and-whitespace stream)
  (read-upto-n-chars stream *source-snippet-size*))
(defun read-snippet-from-string (string &optional position)
  (with-input-from-string (s string)
    (read-snippet s position)))


;;; from swank-source-path-parser.lisp
(defun make-sharpdot-reader (orig-sharpdot-reader)
  #'(lambda (s c n)
      ;; We want things like M-. to work regardless of any #.-fu in
      ;; the source file that is to be visited. (For instance, when a
      ;; file contains #. forms referencing constants that do not
      ;; currently exist in the image.)
      (ignore-errors (funcall orig-sharpdot-reader s c n))))

(defun make-source-recorder (fn source-map)
  "Return a macro character function that does the same as FN, but
additionally stores the result together with the stream positions
before and after of calling FN in the hashtable SOURCE-MAP."
  (declare (type function fn))
  (lambda (stream char)
    (let ((start (1- (file-position stream)))
          (values (multiple-value-list (funcall fn stream char)))
          (end (file-position stream)))
      #+(or)
      (format t "[~D \"~{~A~^, ~}\" ~D ~D ~S]~%"
              start values end (char-code char) char)
      (unless (null values)
        (push (cons start end) (gethash (car values) source-map)))
      (values-list values))))

(defun make-source-recording-readtable (readtable source-map)
  "Return a source position recording copy of READTABLE.
The source locations are stored in SOURCE-MAP."
  (flet ((install-special-sharpdot-reader (*readtable*)
           (let ((old-reader (ignore-errors
                               (get-dispatch-macro-character #\# #\.))))
             (when old-reader
               (set-dispatch-macro-character #\# #\.
                                             (make-sharpdot-reader old-reader))))))
    (let* ((tab (copy-readtable readtable))
           (*readtable* tab))
      (dotimes (code 128)
        (let ((char (code-char code)))
          (multiple-value-bind (fn term) (get-macro-character char tab)
            (when fn
              (set-macro-character char (make-source-recorder fn source-map)
                                   term tab)))))
      (install-special-sharpdot-reader tab)
      tab)))

(defun read-and-record-source-map (stream)
  "Read the next object from STREAM.
Return the object together with a hashtable that maps
subexpressions of the object to stream positions."
  (let* ((source-map (make-hash-table :test #'eq))
         (*readtable* (make-source-recording-readtable *readtable* source-map))
         (start (file-position stream))
         (form (ignore-errors (read stream)))
         (end (file-position stream)))
    ;; ensure that at least FORM is in the source-map
    (unless (gethash form source-map)
      (push (cons start end) (gethash form source-map)))
    (values form source-map)))

(defun skip-toplevel-forms (n stream)
  (let ((*read-suppress* t))
    (dotimes (i n)
      (read stream))))

(defun read-source-form (n stream)
  "Read the Nth toplevel form number with source location recording.
Return the form and the source-map."
  (skip-toplevel-forms n stream)
  (let ((*read-suppress* nil))
    (read-and-record-source-map stream)))

(defun source-path-source-position (path form source-map)
  "Return the start position of PATH from FORM and SOURCE-MAP.  All
subforms along the path are considered and the start and end position
of the deepest (i.e. smallest) possible form is returned."
  ;; compute all subforms along path
  (let ((forms (loop for n in path
                  for f = form then (nth n f)
                  collect f)))
    ;; select the first subform present in source-map
    (loop for form in (reverse forms)
       for positions = (gethash form source-map)
       until (and positions (null (cdr positions)))
       finally (destructuring-bind ((start . end)) positions
                 (return (values start end))))))

(defun check-source-path (path)
  (unless (and (consp path)
               (every #'integerp path))
    (error "The source-path ~S is not valid." path)))

(defun source-path-stream-position (path stream)
  "Search the source-path PATH in STREAM and return its position."
  (check-source-path path)
  (destructuring-bind (tlf-number . path) path
    (multiple-value-bind (form source-map) (read-source-form tlf-number stream)
      (source-path-source-position (cons 0 path) form source-map))))

(defun source-path-string-position (path string)
  (with-input-from-string (s string)
    (source-path-stream-position path s)))

(defun stream-source-position (code-location stream)
  (let* ((cloc (sb-debug::maybe-block-start-location code-location))
         (tlf-number (sb-di::code-location-toplevel-form-offset cloc))
         (form-number (sb-di::code-location-form-number cloc)))
    (multiple-value-bind (tlf pos-map) (read-source-form tlf-number stream)
      (let* ((path-table (sb-di::form-number-translations tlf 0))
             (path (cond ((<= (length path-table) form-number)
                          (warn "inconsistent form-number-translations")
                          (list 0))
                         (t
                          (reverse (cdr (aref path-table form-number)))))))
        (source-path-source-position path tlf pos-map)))))

(defun string-source-position (code-location string)
  (with-input-from-string (s string)
    (stream-source-position code-location s)))

(defun code-location-debug-fun-fun (code-location)
  (sb-di:debug-fun-fun (sb-di:code-location-debug-fun code-location)))



;;; from swank-sbcl.lisp
(defun feature-in-list-p (feature list)
  (etypecase feature
    (symbol (member feature list :test #'eq))
    (cons (flet ((subfeature-in-list-p (subfeature)
                   (feature-in-list-p subfeature list)))
            (ecase (first feature)
              (:or  (some  #'subfeature-in-list-p (rest feature)))
              (:and (every #'subfeature-in-list-p (rest feature)))
              (:not (destructuring-bind (e) (cdr feature)
                      (not (subfeature-in-list-p e)))))))))

(defun shebang-reader (stream sub-character infix-parameter)
  (declare (ignore sub-character))
  (when infix-parameter
    (error "illegal read syntax: #~D!" infix-parameter))
  (let ((next-char (read-char stream)))
    (unless (find next-char "+-")
      (error "illegal read syntax: #!~C" next-char))
    ;; When test is not satisfied
    ;; FIXME: clearer if order of NOT-P and (NOT NOT-P) were reversed? then
    ;; would become "unless test is satisfied"..
    (when (let* ((*package* (find-package "KEYWORD"))
                 (*read-suppress* nil)
                 (not-p (char= next-char #\-))
                 (feature (read stream)))
            (if (feature-in-list-p feature *features*)
                not-p
                (not not-p)))
      ;; Read (and discard) a form from input.
      (let ((*read-suppress* t))
        (read stream t nil t))))
  (values))

(defvar *shebang-readtable*
  (let ((*readtable* (copy-readtable nil)))
    (set-dispatch-macro-character #\# #\!
                                  (lambda (s c n) (shebang-reader s c n))
                                  *readtable*)
    *readtable*))

(defun shebang-readtable ()
  *shebang-readtable*)

(defun sbcl-package-p (package)
  (let ((name (package-name package)))
    (eql (mismatch "SB-" name) 3)))

(defun sbcl-source-file-p (filename)
  (when filename
    (loop for (nil pattern) in (logical-pathname-translations "SYS")
       thereis (pathname-match-p filename pattern))))

(defun guess-readtable-for-filename (filename)
  (if (sbcl-source-file-p filename)
      (shebang-readtable)
      *readtable*))

(defmacro with-definition-source ((&rest names) obj &body body)
  "Like with-slots but works only for structs."
  (flet ((reader (slot)
           ;; Use read-from-string instead of intern so that
           ;; conc-name can be a string such as ext:struct- and not
           ;; cause errors and not force interning ext::struct-
           (read-from-string
            ;; FIXME: no SB-INTROSPECT any more...
            (concatenate 'string "definition-source-"
                         (string slot)))))
    (let ((tmp (gensym "OO-")))
      ` (let ((,tmp ,obj))
          (symbol-macrolet
              ,(loop for name in names collect
                    (typecase name
                      (symbol `(,name (,(reader name) ,tmp)))
                      (cons `(,(first name) (,(reader (second name)) ,tmp)))
                      (t (error "Malformed syntax in WITH-STRUCT: ~A" name))))
            ,@body)))))

(defun categorize-definition-source (definition-source)
  (with-definition-source (pathname form-path character-offset plist)
      definition-source
    (let ((file-p (and pathname (probe-file pathname)
                       (or form-path character-offset))))
      (cond ((and (getf plist :emacs-buffer) file-p) :buffer-and-file)
            ((getf plist :emacs-buffer) :buffer)
            (file-p :file)
            (pathname :file-without-position)
            (t :invalid)))))

(defun definition-source-buffer-location (definition-source)
  (with-definition-source (form-path character-offset plist) definition-source
    (destructuring-bind (&key emacs-buffer emacs-position emacs-directory
                              emacs-string &allow-other-keys)
        plist
      (let ((*readtable* (guess-readtable-for-filename emacs-directory)))
        (multiple-value-bind (start end)
            (if form-path
                (with-debootstrapping
                  (source-path-string-position form-path
                                               emacs-string))
                (values character-offset
                        most-positive-fixnum))
          (make-location
           `(:buffer ,emacs-buffer)
           `(:offset ,emacs-position ,start)
           `(:snippet
             ,(subseq emacs-string
                      start
                      (min end (+ start *source-snippet-size*))))))))))

(defun source-file-position (filename write-date form-path)
  (let ((source (get-source-code filename write-date))
        (*readtable* (guess-readtable-for-filename filename)))
    (with-debootstrapping
      (source-path-string-position form-path source))))

(defun source-hint-snippet (filename write-date position)
  (read-snippet-from-string (get-source-code filename write-date) position))

(defun definition-source-file-location (definition-source)
  (with-definition-source (pathname form-path character-offset plist
                                    file-write-date) definition-source
    (let* ((namestring (namestring (translate-logical-pathname pathname)))
           (pos (if form-path
                    (source-file-position namestring file-write-date
                                          form-path)
                    character-offset))
           (snippet (source-hint-snippet namestring file-write-date pos)))
      (make-location `(:file ,namestring)
                     ;; /file positions/ in Common Lisp start from
                     ;; 0, buffer positions in Emacs start from 1.
                     `(:position ,(1+ pos))
                     `(:snippet ,snippet)))))
(defun definition-source-buffer-and-file-location (definition-source)
  (let ((buffer (definition-source-buffer-location definition-source))
        (file (definition-source-file-location definition-source)))
    (make-location (list :buffer-and-file
                         (cadr (location-buffer buffer))
                         (cadr (location-buffer file)))
                   (location-position buffer)
                   (location-hints buffer))))

(defun definition-source-for-emacs (definition-source type name)
  (with-definition-source (pathname form-path character-offset plist
                                    file-write-date)
      definition-source
    (ecase (categorize-definition-source definition-source)
      (:buffer-and-file
       (definition-source-buffer-and-file-location definition-source))
      (:buffer
       (definition-source-buffer-location definition-source))
      (:file
       (definition-source-file-location definition-source))
      (:file-without-position
       (make-location `(:file ,(namestring
                                (translate-logical-pathname pathname)))
                      '(:position 1)
                      (when (eql type :function)
                        `(:snippet ,(format nil "(defun ~a "
                                            (symbol-name name))))))
      (:invalid
       (error "DEFINITION-SOURCE of ~(~A~) ~A did not contain ~
               meaningful information."
              type name)))))

(defun function-name (f)
  ;; NOTICE: function-name
  (check-type f function)
  (sb-impl::%fun-name f))
(defun function-source-location (function &optional name)
  (declare (type function function))
  (definition-source-for-emacs (find-definition-source function)
      :function
    (or name (function-name function))))
(defun fallback-source-location (code-location)
  (let ((fun (code-location-debug-fun-fun code-location)))
    (cond (fun (function-source-location fun))
          (t (error "Cannot find source location for: ~A " code-location)))))

(defun emacs-buffer-source-location (code-location plist)
  (if (code-location-has-debug-block-info-p code-location)
      (destructuring-bind (&key emacs-buffer emacs-position emacs-string
                                &allow-other-keys)
          plist
        (let* ((pos (string-source-position code-location emacs-string))
               (snipped (read-snippet-from-string emacs-string pos)))
          (make-location `(:buffer ,emacs-buffer)
                         `(:offset ,emacs-position ,pos)
                         `(:snippet ,snipped))))
      (fallback-source-location code-location)))

(defun code-location-debug-source-created (code-location)
  (sb-c::debug-source-created
   (sb-di::code-location-debug-source code-location)))

(defun code-location-debug-source-name (code-location)
  (namestring (truename (sb-c::debug-source-namestring
                         (sb-di::code-location-debug-source code-location)))))

(defun source-file-source-location (code-location)
  (let* ((code-date (code-location-debug-source-created code-location))
         (filename (code-location-debug-source-name code-location))
         (*readtable* (guess-readtable-for-filename filename))
         (source-code (get-source-code filename code-date)))
    (with-debootstrapping
      (with-input-from-string (s source-code)
        (let* ((pos (stream-source-position code-location s))
               (snippet (read-snippet s pos)))
          (make-location `(:file ,filename)
                         `(:position ,pos)
                         `(:snippet ,snippet)))))))

(defun file-source-location (code-location)
  (if (code-location-has-debug-block-info-p code-location)
      (source-file-source-location code-location)
      (fallback-source-location code-location)))

(defun lisp-source-location (code-location)
  (let ((source (prin1-to-string
                 (sb-debug::code-location-source-form code-location 100))))
    (make-location `(:source-form ,source) '(:position 1))))

;;; from swank-sbcl.lisp
(defun code-location-source-location (code-location)
  "FIXME: tweaked..."
  (let* ((dsource (sb-di:code-location-debug-source code-location))
         (plist (sb-c::debug-source-plist dsource)))
    (if (getf plist :emacs-buffer)
        (emacs-buffer-source-location code-location plist)
        (if (sb-di:debug-source-namestring dsource)
            (file-source-location code-location)
            (lisp-source-location code-location)))))



;;; from swank-sbcl.lisp
(defun frame-source-location (index)
  (converting-errors-to-error-location
    (code-location-source-location
     (sb-di:frame-code-location (nth-frame index)))))

(defun debug-var-info (var)
  ;; Introduced by SBCL 1.0.49.76.
  (let ((s (find-symbol "DEBUG-VAR-INFO" :sb-di)))
    (when (and s (fboundp s))
      (funcall s var))))

(defun debug-var-value (var frame location)
  (ecase (sb-di:debug-var-validity var location)
    (:valid (sb-di:debug-var-value var frame))
    ((:invalid :unknown) ':<not-available>)))

(defvar *keep-non-valid-locals* nil)
(defun frame-debug-vars (frame)
  "Return a vector of debug-variables in frame."
  (let ((all-vars (sb-di::debug-fun-debug-vars (sb-di:frame-debug-fun frame))))
    (cond (*keep-non-valid-locals* all-vars)
          (t (let ((loc (sb-di:frame-code-location frame)))
               (remove-if (lambda (var)
                            (ecase (sb-di:debug-var-validity var loc)
                              (:valid nil)
                              ((:invalid :unknown) t)))
                          all-vars))))))

(defun frame-locals (index)
  (let* ((frame (nth-frame index))
         (loc (sb-di:frame-code-location frame))
         (vars (frame-debug-vars frame))
         ;; Since SBCL 1.0.49.76 PREPROCESS-FOR-EVAL understands SB-DEBUG::MORE
         ;; specially.
         (more-name (or (find-symbol "MORE" :sb-debug) 'more))
         (more-context nil)
         (more-count nil)
         (more-id 0))
    (when vars
      (let ((locals
             (loop for v across vars
                do (when (eq (sb-di:debug-var-symbol v) more-name)
                     (incf more-id))
                  (case (debug-var-info v)
                    (:more-context
                     (setf more-context (debug-var-value v frame loc)))
                    (:more-count
                     (setf more-count (debug-var-value v frame loc))))
                collect
                  (list :name (sb-di:debug-var-symbol v)
                        :id (sb-di:debug-var-id v)
                        :value (debug-var-value v frame loc)))))
        (when (and more-context more-count)
          (setf locals (append locals
                               (list
                                (list :name more-name
                                      :id more-id
                                      :value (multiple-value-list
                                              (sb-c:%more-arg-values
                                               more-context
                                               0 more-count)))))))
        locals))))



(defun find-line-position (file char-offset frame)
  ;; It would be nice if SBCL stored line number information in
  ;; addition to form path information by default Since it doesn't
  ;; we need to use Swank to map the source path to a character
  ;; offset, and then map the character offset to a line number
  (ignore-errors
    (let* ((location (sb-di::frame-code-location frame))
           (debug-source (sb-di::code-location-debug-source location))
           (line (with-open-file (stream file)
                   (1+ (loop repeat char-offset
                          count (eql (read-char stream) #\Newline))))))
      (format nil "~:[~a (file modified)~;~a~]"
              (= (file-write-date file)
                 (sb-di::debug-source-created debug-source))
              line))))

(defun print-frame (i)
  (destructuring-bind (&key file position &allow-other-keys)
      (apply #'append
             (remove-if #'atom
                        (frame-source-location i)))
    (let* ((frame (nth-frame i))
           (line-number (find-line-position file position frame)))
      (format t "~2@a: ~s~%~
                   ~:[~*~;~:[~2:*    At ~a (unknown line)~*~%~;~
                             ~2:*    At ~a:~a~%~]~]~
                   ~:[~*~;    Local variables:~%~{      ~a = ~s~%~}~]"
              i
              (sb-debug::frame-call (nth-frame i))
              file line-number
              (frame-locals i)
              (mapcan (lambda (x)
                        ;; Filter out local variables whose variables we
                        ;; don't know
                        (unless (eql (getf x :value) :<not-available>)
                          (list (getf x :name) (getf x :value))))
                      (frame-locals i))))))

;;; Interface
(defun backtrace-with-extra-info (&key (start 1) (end 20))
  (call-with-debugging-environment
   (lambda ()
     (loop for i from start to (length (compute-backtrace
                                        start end))
        do (ignore-errors (print-frame i))))))
