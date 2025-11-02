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

cached class SlabCall extends Call {
    Function targetFunction;
    cached SlabCall() {
        targetFunction = this.getTarget() and
        targetFunction.getADeclarationLocation().getFile().getBaseName() = "slab.h"
    }

    cached abstract Struct getStruct();
    cached abstract string getLabel();

    cached predicate returnsPointer() {
        targetFunction.getType().getPointerIndirectionLevel() > 0
    }
}

cached class KfreeCall extends SlabCall {
    cached KfreeCall() {
        not(this.returnsPointer()) and
        this.getTarget().getName().matches("%free%")
    }

    cached Expr getPointerArgument() {
        exists(Parameter pointer_param|
            this.getTarget().getAParameter() = pointer_param and
            pointer_param.getType().stripType().hasName("void") and
            pointer_param.getType().getPointerIndirectionLevel() > 0 and
            result = this.getArgument(pointer_param.getIndex())
        )
    }

    cached override Struct getStruct() {
        result = this.getPointerArgument().getType().stripType()
    }

    cached override string getLabel() {
        result = "free"
    }
}

cached class KmallocCall extends SlabCall {

    cached KmallocCall() {
        this.returnsPointer() and
        this.getTarget().getName().matches("%alloc%")
    }

    cached override Struct getStruct() {
        result = this.getStructFromConversion() or
        result = this.getStructFromSizeOf()
    }

    cached override string getLabel() {
        result = "alloc"
    }

    cached Struct getStructFromSizeOf() {
        exists(SizeOfNode source, KmallocSizeArgumentNode sink|
            source.getStruct() = result and sink.getCall() = this and
            TaintTracking::localTaint(source, sink)
        )
    }

    cached Struct getStructFromConversion() {
        exists(KmallocCallNode source, ConversionNode sink|
            source.getCall() = this and sink.getStruct() = result and
            // DataFlow::localFlow(source, sink)
            ConversionFlow::flow(source, sink)
        )
    }

    cached Expr getSizeArgument() {
        exists(Parameter size_param|
            this.getTarget().getAParameter() = size_param and
            size_param.getType().getName().matches("size_t") and
            not size_param.getName().matches("n") and
            result = this.getArgument(size_param.getIndex())
        )
    }
}

module ConversionFlow = DataFlow::Global<ConversionFlowConfiguration>;

cached module ConversionFlowConfiguration implements DataFlow::ConfigSig {
    cached predicate isSource(DataFlow::Node source) {
        source instanceof KmallocCallNode
    }
    cached predicate isSink(DataFlow::Node sink) {
        sink instanceof ConversionNode
    }
}

cached class SizeOfNode extends DataFlow::Node {
    Struct struct;
    cached SizeOfNode() {
        exists(SizeofExprOperator sof|
            this.asConvertedExpr() = sof.getExprOperand().getFullyConverted() and
            struct = this.getType().stripType()
        ) or
        exists(SizeofTypeOperator sof|
            this.asExpr() = sof and
            struct = sof.getTypeOperand().stripType()
        )
    }

    cached Struct getStruct() {
        result = struct
    }
}

cached class KmallocSizeArgumentNode extends DataFlow::Node {
    KmallocCall kfc;
    cached KmallocSizeArgumentNode() {
        kfc.getSizeArgument() = this.asExpr()
    }

    cached KmallocCall getCall() {
        result = kfc
    }
}

cached class KmallocCallNode extends DataFlow::Node {
    KmallocCall kfc;
    cached KmallocCallNode() {
        kfc = this.asConvertedExpr()
    }

    cached KmallocCall getCall() {
        result = kfc
    }
}

cached class ConversionNode extends DataFlow::Node {
    Struct struct;
    cached ConversionNode() {
        struct = this.asConvertedExpr().getType().stripType()
    }

    cached Struct getStruct() {
        result = struct
    }
}
