/**
 * @name Linux Kernel slab memory allocations and free
 * @kind problem
 * @problem.severity recommendation
 * @id cpp/kernel/slab-call-sites
 */

import cpp
import semmle.code.cpp.dataflow.new.TaintTracking
import semmle.code.cpp.dataflow.new.DataFlow


from
    SlabCall sfc, Struct struct, Function caller
where
    struct = sfc.getStruct() and
    caller = sfc.getEnclosingFunction()
select
    sfc, "$@: $@() { $@() -> $@ }",
    sfc.getLabel(), sfc.getLabel(),
    caller, caller.getName(),
    sfc, sfc.toString(),
    struct, struct.toString()

class SlabCall extends Call {
    Function targetFunction;
    SlabCall() {
        targetFunction = this.getTarget() and
        targetFunction.getADeclarationLocation().getFile().getBaseName() = "slab.h"
    }

    abstract Struct getStruct();
    abstract string getLabel();

    predicate returnsPointer() {
        targetFunction.getType().getPointerIndirectionLevel() > 0
    }
}

class KfreeCall extends SlabCall {
    KfreeCall() {
        not(this.returnsPointer()) and
        this.getTarget().getName().matches("%free%")
    }

    Expr getPointerArgument() {
        exists(Parameter pointer_param|
            this.getTarget().getAParameter() = pointer_param and
            pointer_param.getType().stripType().hasName("void") and
            pointer_param.getType().getPointerIndirectionLevel() > 0 and
            result = this.getArgument(pointer_param.getIndex())
        )
    }

    override Struct getStruct() {
        result = this.getPointerArgument().getType().stripType()
    }

    override string getLabel() {
        result = "free"
    }
}

class KmallocCall extends SlabCall {

    KmallocCall() {
        this.returnsPointer() and
        this.getTarget().getName().matches("%alloc%")
    }

    override Struct getStruct() {
        result = this.getStructFromConversion() or
        result = this.getStructFromSizeOf()
    }

    override string getLabel() {
        result = "alloc"
    }

    Struct getStructFromSizeOf() {
        exists(SizeOfNode source, KmallocSizeArgumentNode sink|
            source.getStruct() = result and sink.getCall() = this and
            TaintTracking::localTaint(source, sink)
        )
    }

    Struct getStructFromConversion() {
        exists(KmallocCallNode source, ConversionNode sink|
            source.getCall() = this and sink.getStruct() = result and
            DataFlow::localFlow(source, sink)
        )
    }

    Expr getSizeArgument() {
        exists(Parameter size_param|
            this.getTarget().getAParameter() = size_param and
            size_param.getType().getName().matches("size_t") and
            not size_param.getName().matches("n") and
            result = this.getArgument(size_param.getIndex())
        )
    }
}

class SizeOfNode extends DataFlow::Node {
    Struct struct;
    SizeOfNode() {
        exists(SizeofExprOperator sof|
            this.asConvertedExpr() = sof.getExprOperand().getFullyConverted() and
            struct = this.getType().stripType()
        ) or
        exists(SizeofTypeOperator sof|
            this.asExpr() = sof and
            struct = sof.getTypeOperand().stripType()
        )
    }

    Struct getStruct() {
        result = struct
    }
}

class KmallocSizeArgumentNode extends DataFlow::Node {
    KmallocCall kfc;
    KmallocSizeArgumentNode() {
        kfc.getSizeArgument() = this.asExpr()
    }

    KmallocCall getCall() {
        result = kfc
    }
}

class KmallocCallNode extends DataFlow::Node {
    KmallocCall kfc;
    KmallocCallNode() {
        kfc = this.asConvertedExpr()
    }

    KmallocCall getCall() {
        result = kfc
    }
}

class ConversionNode extends DataFlow::Node {
    Struct struct;
    ConversionNode() {
        struct = this.asConvertedExpr().getType().stripType()
    }

    Struct getStruct() {
        result = struct
    }
}
