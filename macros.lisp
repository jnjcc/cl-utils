;;; ONCE-ONLY from Practical Common Lisp
(defmacro once-only-pcl ((&rest names) &body body)
  "Used to generate code that evaluates certain macro arguments
once only and in a particular order"
  (let ((gensyms (loop for n in names collect (gensym))))
    `(let (,@(loop for g in gensyms collect `(,g (gensym))))
       `(let (,,@(loop for g in gensyms for n in names collect ``(,,g ,,n)))
          ,(let (,@(loop for n in names for g in gensyms collect `(,n ,g)))
                ,@body)))))

;;; modified NAMED-LET from SBCL
(defmacro named-let (name binds &body body)
  `(labels ((,name ,(mapcar #'first binds) ,@body))
     (,name ,@(mapcar #'second binds))))
;;; modified ONCE-ONLY from SBCL
(defmacro once-only (specs &body body)
  (named-let frob ((specs specs)
                   (body body))
    (if (null specs)
        `(progn ,@body)
        (let ((spec (first specs)))
          (let* ((name (first spec))
                 (exp-temp (gensym "ONCE-ONLY")))
            `(let ((,exp-temp ,(second spec))
                   (,name (gensym ,(symbol-name name))))
               `(let ((,,name ,,exp-temp))
                  ,,(frob (rest specs) body))))))))

