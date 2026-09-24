// Exploratory probe, not replay evidence: which native ReLU lemmas do tiny runs emit?
// Built outside the capture harness; see notes/RELU_AUX_LOWER_BOUND_PROPAGATION.md.
#include "Engine.h"
#include "InputQuery.h"
#include "ReluConstraint.h"

#include <iostream>
#include <string>

static const char *kind( Tightening::BoundType t )
{
    return t == Tightening::UB ? "U" : "L";
}

static void dump( const UnsatCertificateNode *node, unsigned depth )
{
    std::string pad( 2 * depth, ' ' );
    for ( const auto &t : node->getSplit().getBoundTightenings() )
        std::cout << pad << "split x" << t._variable << " " << kind( t._type ) << " " << t._value << "\n";
    for ( const auto &lemma : node->getPLCLemmas() )
    {
        std::cout << pad << "lemma cause x" << lemma->getCausingVars().front() << " "
                  << kind( lemma->getCausingVarBound() ) << " -> x" << lemma->getAffectedVar() << " "
                  << kind( lemma->getAffectedVarBound() ) << " bound " << lemma->getBound() << " expl [";
        for ( const auto &entry : lemma->getExplanations().front() )
            std::cout << " row" << entry._index << ":" << entry._value;
        std::cout << " ]\n";
    }
    if ( node->getContradiction() )
    {
        const auto &c = node->getContradiction()->getContradiction();
        std::cout << pad << "contradiction ";
        if ( c.empty() )
            std::cout << "var x" << node->getContradiction()->getVar();
        else
            for ( const auto &entry : c )
                std::cout << " row" << entry._index << ":" << entry._value;
        std::cout << "\n";
    }
    if ( node->getDelegationStatus() != DONT_DELEGATE )
        std::cout << pad << "DELEGATED\n";
    for ( const auto *child : node->getChildren() )
        dump( child, depth + 1 );
}

int main( int argc, char **argv )
{
    std::string scenario = argc > 1 ? argv[1] : "";
    Options::get()->setBool( Options::PRODUCE_PROOFS, true );
    Options::get()->setInt( Options::VERBOSITY, 0 );
    Options::get()->setString( Options::LP_SOLVER, "native" );
    Options::get()->setString( Options::SYMBOLIC_BOUND_TIGHTENING_TYPE, "none" );
    GlobalConfiguration::USE_DEEPSOI_LOCAL_SEARCH = false;

    InputQuery input;
    input.setNumberOfVariables( 5 );
    double lower[5], upper[5];
    List<List<Equation::Addend>> rows;
    String relu;
    if ( scenario == "output_negative" || scenario == "output_negative_nonneg" )
    {
        // f=x0, b=x1, aux=x2, w=x3, z=x4: f=w<=-1/4, b=z>=1/8.
        double l[] = { scenario == "output_negative" ? -1.0 : 0.0, -2, 0, -2, 0.125 };
        double u[] = { 2, 2, 2, -0.25, 2 };
        for ( unsigned i = 0; i < 5; ++i ) { lower[i] = l[i]; upper[i] = u[i]; }
        rows = { { { 1, 0 }, { -1, 1 }, { -1, 2 } }, { { 1, 0 }, { -1, 3 } }, { { 1, 1 }, { -1, 4 } } };
        relu = "relu,0,1,2";
    }
    else if ( scenario == "aux_zero" || scenario == "aux_zero_nonneg" )
    {
        // aux=x0, b=x1, f=x2, w=x3, z=x4: aux=w<=0, b=z<=-1/8.
        double l[] = { 0, -2, scenario == "aux_zero" ? -1.0 : 0.0, -2, -2 };
        double u[] = { 2, 2, 2, 0, -0.125 };
        for ( unsigned i = 0; i < 5; ++i ) { lower[i] = l[i]; upper[i] = u[i]; }
        rows = { { { 1, 2 }, { -1, 1 }, { -1, 0 } }, { { 1, 0 }, { -1, 3 } }, { { 1, 1 }, { -1, 4 } } };
        relu = "relu,2,1,0";
    }
    else
    {
        std::cerr << "unknown scenario\n";
        return 2;
    }
    for ( unsigned i = 0; i < 5; ++i )
    {
        input.setLowerBound( i, lower[i] );
        input.setUpperBound( i, upper[i] );
    }
    for ( const auto &terms : rows )
    {
        Equation equation;
        for ( const auto &term : terms ) equation.addAddend( term._coefficient, term._variable );
        equation.setScalar( 0 );
        input.addEquation( equation );
    }
    input.addPiecewiseLinearConstraint( new ReluConstraint( relu ) );

    Engine engine;
    engine.setRandomSeed( 1 );
    if ( !engine.processInputQuery( input, false ) )
    {
        std::cout << "initialization UNSAT\n";
        return 0;
    }
    const auto *initial = engine.getUNSATCertificateRoot();
    std::cout << "lemmas before solve: " << ( initial ? initial->getPLCLemmas().size() : 0 ) << "\n";
    bool sat = engine.solve( 10 );
    std::cout << "solve: " << sat << " exit " << engine.getExitCode() << "\n";
    if ( engine.getUNSATCertificateRoot() )
        dump( engine.getUNSATCertificateRoot(), 0 );
    return 0;
}
