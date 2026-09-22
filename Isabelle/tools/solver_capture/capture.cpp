// Capture a real proof-producing Engine::solve execution using public APIs.
// No Contradiction, PLCLemma, or certificate node is constructed by this harness.
#include "CSRMatrix.h"
#include "Engine.h"
#include "EngineState.h"
#include "File.h"
#include "InputQuery.h"
#include "JsonWriter.h"
#include "ReluConstraint.h"

#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>

static void require( bool condition, const char *message )
{
    if ( !condition ) throw std::runtime_error( message );
}

static void write_number( std::ostream &out, double value )
{
    require( std::isfinite( value ), "nonfinite processed query value" );
    out << std::setprecision( 17 ) << value;
}

// Independently serialize the processed query BEFORE solve(), without obtaining
// a header from a certificate. Query row order is Engine::createConstraintMatrix
// order; duplicate columns are rejected instead of silently choosing a value.
static void snapshot( const Query &query, const std::string &path,
                      CSRMatrix &matrix, Vector<double> &upper, Vector<double> &lower )
{
    unsigned n = query.getNumberOfVariables(), m = query.getNumberOfEquations();
    require( n > 0 && m > 0, "empty processed query" );
    Vector<double> rows( n * m, 0 );
    std::ofstream out( path );
    require( bool( out ), "cannot open processed query" );
    out << "{\n  \"tableau\": [";
    unsigned row = 0;
    for ( const auto &equation : query.getEquations() )
    {
        require( equation._type == Equation::EQ && equation._scalar == 0,
                 "expected homogeneous processed equality" );
        out << ( row ? ",\n    [" : "\n    [" );
        std::set<unsigned> seen;
        bool first = true;
        for ( const auto &term : equation._addends )
        {
            require( term._variable < n && seen.insert( term._variable ).second,
                     "invalid or duplicate processed column" );
            rows[row * n + term._variable] = term._coefficient;
        }
        // CSRMatrix/JsonWriter use column order.
        for ( unsigned j = 0; j < n; ++j )
            if ( rows[row * n + j] != 0 )
            {
                if ( !first ) out << ", ";
                first = false;
                out << "{\"var\": " << j << ", \"val\": ";
                write_number( out, rows[row * n + j] );
                out << "}";
            }
        out << "]";
        ++row;
    }
    out << "\n  ],\n  \"upperBounds\": [";
    for ( unsigned j = 0; j < n; ++j )
    {
        upper.append( query.getUpperBound( j ) );
        lower.append( query.getLowerBound( j ) );
        if ( j ) out << ", ";
        write_number( out, upper[j] );
    }
    out << "],\n  \"lowerBounds\": [";
    for ( unsigned j = 0; j < n; ++j )
    {
        if ( j ) out << ", ";
        write_number( out, lower[j] );
    }
    out << "],\n  \"constraints\": [";
    bool first = true;
    for ( const auto *constraint : query.getPiecewiseLinearConstraints() )
    {
        require( constraint->getType() == RELU, "only ReLU supported" );
        if ( !first ) out << ", ";
        first = false;
        out << "{\"constraintType\": 0, \"vars\": [";
        bool firstVar = true;
        for ( unsigned v : constraint->getParticipatingVariables() )
        {
            if ( !firstVar ) out << ", ";
            firstVar = false;
            out << v;
        }
        for ( unsigned v : constraint->getTableauAuxVars() ) out << ", " << v;
        out << "]}";
    }
    out << "]\n}\n";
    out.close();
    require( bool( out ), "cannot write processed query" );
    matrix.initialize( rows.data(), m, n );
}

int main( int argc, char **argv )
{
    try
    {
        require( argc == 2 || argc == 3,
                 "usage: marabou_solver_capture OUTPUT_DIRECTORY [linear|relu|relu_aux|relu_aux_active|relu_split]" );
        std::string directory = argv[1];
        std::string scenario = argc == 3 ? argv[2] : "linear";
        require( scenario == "linear" || scenario == "relu" ||
                 scenario == "relu_aux" || scenario == "relu_aux_active" ||
                 scenario == "relu_split", "unknown scenario" );
        bool reluScenario = scenario != "linear";
        bool auxiliaryScenario = scenario == "relu_aux" || scenario == "relu_aux_active";
        bool activeScenario = scenario == "relu_aux_active";
        bool splitScenario = scenario == "relu_split";
        std::string prefix = directory + "/solver_" + scenario;
        Options::get()->setBool( Options::PRODUCE_PROOFS, true );
        Options::get()->setInt( Options::VERBOSITY, 0 );
        Options::get()->setString( Options::LP_SOLVER, "native" );
        Options::get()->setString( Options::SYMBOLIC_BOUND_TIGHTENING_TYPE, "none" );
        GlobalConfiguration::USE_DEEPSOI_LOCAL_SEARCH = false;
        if ( splitScenario )
            Options::get()->setInt( Options::CONSTRAINT_VIOLATION_THRESHOLD, 1 );

        // Initialization must succeed; UNSAT and its evidence must come from solve().
        InputQuery input;
        if ( !reluScenario )
        {
            input.setNumberOfVariables( 2 );
            input.setLowerBound( 0, -2 );
            input.setUpperBound( 0, 0.25 );
            input.setLowerBound( 1, 0.5 );
            input.setUpperBound( 1, 2 );
            Equation equation;
            equation.addAddend( 1, 0 );
            equation.addAddend( -1, 1 );
            equation.setScalar( 0 );
            input.addEquation( equation );
        }
        else if ( splitScenario )
        {
            // b=x0, f=x1, a=x2, t=x3, u=x4, nonnegative slacks x5..x8.
            // f >= |t|+1/4 and a >= |u|+1/4 exclude both ReLU phases.
            // The interval bounds leave f/a at lower bound zero initially.
            input.setNumberOfVariables( 9 );
            const double lower[] = { -1, 0, 0, -1, -1, 0, 0, 0, 0 };
            const double upper[] = { 1, 1, 1, 1, 1, 2, 2, 2, 2 };
            for ( unsigned i = 0; i < 9; ++i )
            {
                input.setLowerBound( i, lower[i] );
                input.setUpperBound( i, upper[i] );
            }
            for ( const auto &terms : {
                List<Equation::Addend>{ { 1, 1 }, { -1, 3 }, { -1, 5 } },
                List<Equation::Addend>{ { 1, 1 }, { 1, 3 }, { -1, 6 } },
                List<Equation::Addend>{ { 1, 2 }, { -1, 4 }, { -1, 7 } },
                List<Equation::Addend>{ { 1, 2 }, { 1, 4 }, { -1, 8 } } } )
            {
                Equation equation;
                for ( const auto &term : terms ) equation.addAddend( term._coefficient, term._variable );
                equation.setScalar( 0.25 );
                input.addEquation( equation );
            }
            Equation auxiliary;
            auxiliary.addAddend( 1, 1 );
            auxiliary.addAddend( -1, 0 );
            auxiliary.addAddend( -1, 2 );
            auxiliary.setScalar( 0 );
            input.addEquation( auxiliary );
            input.addPiecewiseLinearConstraint( new ReluConstraint( String( "relu,1,0,2" ) ) );
        }
        else
        {
            // b=x0, f=x1, z=x2, w=x3, aux=x4.
            // The root b/f bounds leave the phase unknown. Negative variants
            // use b=z<=-1/2 and f=w>=1/4; the active variant uses b=z>=1/2
            // and aux=w>=1/4. All include f-b-aux=0 and f=ReLU(b).
            input.setNumberOfVariables( 5 );
            double lower[] = { -1, 0, -1, 0.25, 0 };
            double upper[] = { 2, 2, -0.5, 2, 1 };
            if ( scenario == "relu_aux" )
            {
                lower[0] = lower[2] = -2;
                upper[4] = 2;
            }
            if ( activeScenario )
            {
                lower[2] = 0.5;
                upper[2] = upper[4] = 2;
            }
            for ( unsigned i = 0; i < 5; ++i )
            {
                input.setLowerBound( i, lower[i] );
                input.setUpperBound( i, upper[i] );
            }
            // Preserve the earlier relu case's row order. The broader negative
            // case recreates the previously unsupported auxiliary-upper lemma;
            // the active case makes an auxiliary-upper lemma essential.
            List<List<Equation::Addend>> rows{ { { 1, 0 }, { -1, 2 } } };
            List<Equation::Addend> auxiliaryRow{ { 1, 1 }, { -1, 0 }, { -1, 4 } };
            List<Equation::Addend> outputRow{ { 1, activeScenario ? 4u : 1u }, { -1, 3 } };
            if ( !auxiliaryScenario )
                rows.append( auxiliaryRow );
            rows.append( outputRow );
            if ( auxiliaryScenario )
                rows.append( auxiliaryRow );
            for ( const auto &terms : rows )
            {
                Equation equation;
                for ( const auto &term : terms ) equation.addAddend( term._coefficient, term._variable );
                equation.setScalar( 0 );
                input.addEquation( equation );
            }
            input.addPiecewiseLinearConstraint( new ReluConstraint( String( "relu,1,0,4" ) ) );
        }

        Engine engine;
        engine.setRandomSeed( 1 );
        require( engine.shouldProduceProofs(), "proof production disabled" );
        require( engine.processInputQuery( input, false ), "initialization found UNSAT before solve" );
        require( !engine.preprocessingEnabled(), "unexpected preprocessing" );
        Query processed( *engine.getQuery() );
        if ( reluScenario )
            require( processed.getPiecewiseLinearConstraints().size() == 1 &&
                     !processed.getPiecewiseLinearConstraints().front()->phaseFixed(),
                     "ReLU phase fixed before solving" );
        const auto *initialRoot = engine.getUNSATCertificateRoot();
        require( initialRoot && initialRoot->getPLCLemmas().empty() &&
                 initialRoot->getChildren().empty() && !initialRoot->getContradiction(),
                 "unexpected proof evidence before solve" );
        CSRMatrix matrix;
        Vector<double> upper, lower;
        snapshot( processed, prefix + "_query.json", matrix, upper, lower );
        EngineState initial;
        engine.storeState( initial, TableauStateStorageLevel::STORE_ENTIRE_TABLEAU_STATE );
        const auto &tableau = initial._tableauState;
        require( tableau._n == processed.getNumberOfVariables() &&
                 tableau._m == processed.getNumberOfEquations(), "snapshot dimensions differ" );
        for ( unsigned i = 0; i < tableau._m; ++i )
        {
            require( tableau._b[i] == 0, "nonzero tableau right-hand side" );
            for ( unsigned j = 0; j < tableau._n; ++j )
                require( matrix.get( i, j ) == tableau._A->get( i, j ),
                         "query snapshot differs from the engine tableau" );
        }
        for ( unsigned j = 0; j < tableau._n; ++j )
            require( upper[j] == engine.getGroundBound( j, true ) &&
                     lower[j] == engine.getGroundBound( j, false ),
                     "query snapshot differs from initial ground bounds" );
        bool sat = engine.solve( 10 );
        require( !sat && engine.getExitCode() == Engine::UNSAT, "solve did not return UNSAT" );
        const auto *root = engine.getUNSATCertificateRoot();
        require( root != nullptr, "solver produced no certificate" );
        std::cout << "Native root children: " << root->getChildren().size()
                  << "; root lemmas: " << root->getPLCLemmas().size()
                  << "; splits: " << engine.getStatistics()->getUnsignedAttribute( Statistics::NUM_SPLITS )
                  << "; simplex steps: " << engine.getStatistics()->getLongAttribute( Statistics::NUM_SIMPLEX_STEPS )
                  << "\n";
        require( root->getVisited() && !root->getSATSolutionFlag() &&
                 root->getDelegationStatus() == DONT_DELEGATE,
                 "expected a visited, nondelegated UNSAT node" );
        if ( splitScenario )
        {
            require( root->getChildren().size() == 2 && !root->getContradiction(),
                     "expected a binary native split" );
            require( root->getPLCLemmas().empty(), "unexpected root lemmas" );
            for ( const auto *child : root->getChildren() )
                require( child && child->getVisited() && !child->getSATSolutionFlag() &&
                         child->getDelegationStatus() == DONT_DELEGATE &&
                         child->getChildren().empty() && child->getContradiction() &&
                         child->getPLCLemmas().empty(),
                         "expected two closed, nondelegated linear children" );
        }
        else
            require( root->getChildren().empty() && root->getContradiction(),
                     "expected a closed leaf" );
        if ( !reluScenario )
            require( root->getPLCLemmas().empty(), "unexpected nonlinear evidence in linear case" );
        else if ( !splitScenario )
        {
            unsigned expected = scenario == "relu_aux" ? 2 : 1;
            require( root->getPLCLemmas().size() == expected, "unexpected native ReLU lemma count" );
            unsigned index = 0;
            for ( const auto &lemma : root->getPLCLemmas() )
            {
                bool auxiliaryLemma = auxiliaryScenario && index == 0;
                require( lemma && lemma->getConstraintType() == RELU &&
                         lemma->getCausingVars().size() == 1 && lemma->getCausingVars().front() == 0 &&
                         lemma->getAffectedVar() == ( auxiliaryLemma ? 4u : 1u ) &&
                         lemma->getCausingVarBound() == ( auxiliaryLemma ? Tightening::LB : Tightening::UB ) &&
                         lemma->getAffectedVarBound() == Tightening::UB &&
                         ( auxiliaryLemma && !activeScenario ? lemma->getBound() > 0 : lemma->getBound() == 0 ) &&
                         lemma->getExplanations().size() == 1 &&
                         !lemma->getExplanations().front().empty(),
                         "unexpected explained ReLU propagation pattern" );
                ++index;
            }
        }
        File proofFile( ( prefix + ".json" ).c_str() );
        JsonWriter::writeProofToJson( root, processed.getNumberOfEquations(), &matrix,
                                     upper, lower, processed.getPiecewiseLinearConstraints(), proofFile );
        const auto *statistics = engine.getStatistics();
        require( statistics->getUnsignedAttribute( Statistics::NUM_CERTIFIED_LEAVES ) == ( splitScenario ? 2u : 1u ) &&
                 statistics->getUnsignedAttribute( Statistics::NUM_DELEGATED_LEAVES ) == 0,
                 "unexpected explained leaf count or delegation" );
        std::ofstream report( prefix + "_run.json" );
        report << "{\n"
               << "  \"scenario\": \"" << scenario << "\",\n"
               << "  \"proof_production\": true,\n"
               << "  \"preprocessing\": false,\n"
               << "  \"deepsoi\": false,\n"
               << "  \"initialization_succeeded\": true,\n"
               << "  \"solve_return\": false,\n"
               << "  \"exit_code\": \"UNSAT\",\n"
               << "  \"timeout_seconds\": 10,\n"
               << "  \"seed\": 1,\n"
               << "  \"input_variables\": " << input.getNumberOfVariables() << ",\n"
               << "  \"processed_variables\": " << processed.getNumberOfVariables() << ",\n"
               << "  \"processed_rows\": " << processed.getNumberOfEquations() << ",\n"
               << "  \"relu_constraints\": " << processed.getPiecewiseLinearConstraints().size() << ",\n"
               << "  \"relu_phase_unfixed_before_solve\": " << ( reluScenario ? "true" : "null" ) << ",\n"
               << "  \"plc_lemmas_before_solve\": 0,\n"
               << "  \"plc_lemmas_after_solve\": " << root->getPLCLemmas().size() << ",\n"
               << "  \"root_children\": " << root->getChildren().size() << ",\n"
               << "  \"main_loop_iterations\": "
               << statistics->getLongAttribute( Statistics::NUM_MAIN_LOOP_ITERATIONS ) << ",\n"
               << "  \"simplex_steps\": "
               << statistics->getLongAttribute( Statistics::NUM_SIMPLEX_STEPS ) << ",\n"
               << "  \"explicit_basis_tightening_calls\": "
               << statistics->getLongAttribute( Statistics::NUM_BOUND_TIGHTENINGS_ON_EXPLICIT_BASIS ) << ",\n"
               << "  \"explained_leaves\": "
               << statistics->getUnsignedAttribute( Statistics::NUM_CERTIFIED_LEAVES ) << ",\n"
               << "  \"delegated_leaves\": 0,\n"
               << "  \"initial_snapshot_matches_tableau_and_ground_bounds\": true\n"
               << "}\n";
        report.close();
        require( bool( report ), "cannot write run report" );
        std::cout << "Engine::processInputQuery(input, false): true\n"
                  << "Engine::solve(10): false; exit code UNSAT\n"
                  << "Proof production: true; preprocessing: false; DeepSoI: false\n"
                  << "Processed variables: " << processed.getNumberOfVariables()
                  << "; rows: " << processed.getNumberOfEquations() << "\n"
                  << "PLC lemmas: 0 before solve; " << root->getPLCLemmas().size() << " after solve\n"
                  << "Main-loop iterations: "
                  << engine.getStatistics()->getLongAttribute( Statistics::NUM_MAIN_LOOP_ITERATIONS )
                  << "; simplex steps: "
                  << engine.getStatistics()->getLongAttribute( Statistics::NUM_SIMPLEX_STEPS ) << "\n"
                  << "Initial query/tableau/ground-bound snapshot comparison: exact match\n"
                  << "Captured unmodified solver certificate and pre-solve query snapshot.\n";
        return 0;
    }
    catch ( const std::exception &error )
    {
        std::cerr << "Capture failed: " << error.what() << "\n";
        return 1;
    }
}
