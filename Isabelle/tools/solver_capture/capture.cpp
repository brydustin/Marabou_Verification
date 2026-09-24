// Capture a real proof-producing Engine::solve execution using public APIs.
// No Contradiction, PLCLemma, or certificate node is constructed by this harness.
#include "CSRMatrix.h"
#include "Engine.h"
#include "EngineState.h"
#include "File.h"
#include "InfeasibleQueryException.h"
#include "InputQuery.h"
#include "JsonWriter.h"
#include "Preprocessor.h"
#include "ReluConstraint.h"

#include <algorithm>
#include <cmath>
#include <fstream>
#include <gmpxx.h>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <map>
#include <memory>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

static void require( bool condition, const char *message )
{
    if ( !condition ) throw std::runtime_error( message );
}

static void write_number( std::ostream &out, double value )
{
    require( std::isfinite( value ), "nonfinite query value" );
    out << std::setprecision( 17 ) << value;
}

// Save the actual InputQuery before Engine initialization. Preserve addend order
// and the original right-hand sides; do not infer this query from the tableau.
static void snapshot_source( const IQuery &input, const std::string &path, bool plainRelu = false )
{
    // The implemented read API copies the InputQuery without preprocessing.
    const std::unique_ptr<Query> copy( input.generateQuery() );
    const Query &query = *copy;
    require( query.getNonlinearConstraints().empty(), "unsupported source nonlinear constraint" );
    unsigned n = query.getNumberOfVariables();
    const auto &equations = query.getEquations();
    require( n > 0 && !equations.empty(), "empty source query" );
    std::ofstream out( path );
    require( bool( out ), "cannot open source query" );
    out << "{\n  \"format\": \""
        << ( plainRelu ? "marabou-plain-relu-query-v1" : "marabou-source-query-v1" ) << "\",\n"
        << "  \"variables\": " << n << ",\n  \"equations\": [";
    bool first = true;
    for ( const auto &equation : equations )
    {
        require( equation._type == Equation::EQ, "only source equalities supported" );
        out << ( first ? "\n    " : ",\n    " );
        first = false;
        out << "{\"type\": \"EQ\", \"addends\": [";
        std::set<unsigned> seen;
        bool firstTerm = true;
        for ( const auto &term : equation._addends )
        {
            require( term._variable < n && seen.insert( term._variable ).second,
                     "invalid or duplicate source column" );
            if ( !firstTerm ) out << ", ";
            firstTerm = false;
            out << "{\"var\": " << term._variable << ", \"val\": ";
            write_number( out, term._coefficient );
            out << "}";
        }
        out << "], \"scalar\": ";
        write_number( out, equation._scalar );
        out << "}";
    }
    out << "\n  ],\n  \"upperBounds\": [";
    for ( unsigned j = 0; j < n; ++j )
    {
        if ( j ) out << ", ";
        write_number( out, query.getUpperBound( j ) );
    }
    out << "],\n  \"lowerBounds\": [";
    for ( unsigned j = 0; j < n; ++j )
    {
        if ( j ) out << ", ";
        write_number( out, query.getLowerBound( j ) );
    }
    out << "],\n  \"constraints\": [";
    first = true;
    for ( const auto *constraint : query.getPiecewiseLinearConstraints() )
    {
        require( constraint->getType() == RELU &&
                 constraint->getParticipatingVariables().size() == ( plainRelu ? 2u : 3u ) &&
                 constraint->getTableauAuxVars().empty(),
                 "unexpected source ReLU auxiliary form" );
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
        out << "]}";
    }
    out << "]\n}\n";
    out.close();
    require( bool( out ), "cannot write source query" );
}

// Run the real native transformation on a query with no ReLU auxiliary.
// Its equation and bounds are created exclusively by the upstream method.
static void introduce_native_relu_aux( Query &query, const std::string &prefix )
{
    require( query.getPiecewiseLinearConstraints().size() == 1 &&
             query.getPiecewiseLinearConstraints().front()->getType() == RELU,
             "expected one plain ReLU" );
    auto *relu = static_cast<ReluConstraint *>( query.getPiecewiseLinearConstraints().front() );
    require( !relu->auxVariableInUse(), "ReLU auxiliary already present" );
    const unsigned beforeVariables = query.getNumberOfVariables();
    const unsigned beforeRows = query.getNumberOfEquations();
    snapshot_source( query, prefix + "_before_relu.json", true );

    // Use the same bound-notification helper as Preprocessor::preprocess.
    // General preprocessing is not invoked.
    Preprocessor::informConstraintsOfInitialBounds( query );
    const double inputLower = query.getLowerBound( relu->getB() );
    require( std::isfinite( inputLower ), "capture requires a finite input lower bound" );
    relu->transformToUseAuxVariables( query );
    require( relu->auxVariableInUse() && relu->getAux() == beforeVariables &&
             query.getNumberOfVariables() == beforeVariables + 1 &&
             query.getNumberOfEquations() == beforeRows + 1,
             "unexpected native ReLU introduction result" );

    std::ofstream out( prefix + "_relu_step.json" );
    require( bool( out ), "cannot open ReLU introduction record" );
    out << "{\n  \"format\": \"marabou-relu-aux-introduction-v1\",\n"
        << "  \"input\": " << relu->getB() << ",\n"
        << "  \"output\": " << relu->getF() << ",\n"
        << "  \"auxiliary\": " << relu->getAux() << ",\n"
        << "  \"lower\": ";
    write_number( out, inputLower );
    out << "\n}\n";
    out.close();
    require( bool( out ), "cannot write ReLU introduction record" );
}

// Record the actual native calls in order. Full before/after queries are
// captured independently; neither this list nor native metadata is trusted.
static void introduce_native_relu_aux_sequence( Query &query, const std::string &prefix )
{
    require( !query.getPiecewiseLinearConstraints().empty(), "expected plain ReLUs" );
    for ( const auto *constraint : query.getPiecewiseLinearConstraints() )
        require( constraint->getType() == RELU &&
                 !static_cast<const ReluConstraint *>( constraint )->auxVariableInUse(),
                 "expected a plain ReLU without an auxiliary" );
    snapshot_source( query, prefix + "_before_relu.json", true );
    Preprocessor::informConstraintsOfInitialBounds( query );
    std::ofstream out( prefix + "_relu_steps.json" );
    require( bool( out ), "cannot open ReLU introduction sequence" );
    out << "{\n  \"format\": \"marabou-relu-aux-sequence-v1\",\n  \"steps\": [";
    bool first = true;
    for ( auto *constraint : query.getPiecewiseLinearConstraints() )
    {
        auto *relu = static_cast<ReluConstraint *>( constraint );
        const unsigned beforeVariables = query.getNumberOfVariables();
        const unsigned beforeRows = query.getNumberOfEquations();
        const double inputLower = query.getLowerBound( relu->getB() );
        require( std::isfinite( inputLower ), "capture requires finite input lower bounds" );
        relu->transformToUseAuxVariables( query );
        require( relu->auxVariableInUse() && relu->getAux() == beforeVariables &&
                 query.getNumberOfVariables() == beforeVariables + 1 &&
                 query.getNumberOfEquations() == beforeRows + 1,
                 "unexpected native ReLU introduction result" );
        out << ( first ? "\n    " : ",\n    " )
            << "{\"input\": " << relu->getB() << ", \"output\": " << relu->getF()
            << ", \"auxiliary\": " << relu->getAux() << ", \"lower\": ";
        write_number( out, inputLower );
        out << "}";
        first = false;
    }
    out << "\n  ]\n}\n";
    out.close();
    require( bool( out ), "cannot write ReLU introduction sequence" );
}

// The initial basis Engine::processInputQuery chose, in native index order
// (Tableau::_basicIndexToVariable and _nonBasicIndexToVariable after
// initializeTableau). HOL recomputes it from the source query; the record is
// only compared, never trusted.
static void snapshot_initial_basis( const TableauState &tableau, unsigned sourceVariables,
                                    const std::string &path )
{
    std::ofstream out( path );
    require( bool( out ), "cannot open initial basis" );
    out << "{\n  \"format\": \"marabou-initial-basis-v1\",\n  \"source_variables\": "
        << sourceVariables << ",\n  \"rows\": " << tableau._m << ",\n  \"basic\": [";
    for ( unsigned i = 0; i < tableau._m; ++i )
        out << ( i ? ", " : "" ) << tableau._basicIndexToVariable[i];
    out << "],\n  \"nonbasic\": [";
    for ( unsigned i = 0; i < tableau._n - tableau._m; ++i )
        out << ( i ? ", " : "" ) << tableau._nonBasicIndexToVariable[i];
    out << "]\n}\n";
    out.close();
    require( bool( out ), "cannot write initial basis" );
}

// Propose one introduction per observed new tableau column. This is a harness
// proposal, not a native transformation log. The importer and HOL replay must
// check its complete result against the separately captured processed query.
static void snapshot_steps( unsigned sourceVariables, unsigned sourceRows,
                            const Query &processed, const std::string &path )
{
    require( processed.getNumberOfEquations() == sourceRows &&
             processed.getNumberOfVariables() == sourceVariables + sourceRows,
             "unsupported initialization dimensions" );
    std::ofstream out( path );
    require( bool( out ), "cannot open introduction list" );
    out << "{\n  \"format\": \"marabou-fixed-aux-sequence-v1\",\n  \"steps\": [";
    std::set<unsigned> introduced;
    unsigned row = 0;
    for ( const auto &equation : processed.getEquations() )
    {
        unsigned fresh = 0, count = 0;
        for ( const auto &term : equation._addends )
            if ( term._variable >= sourceVariables )
            {
                require( term._variable < processed.getNumberOfVariables() &&
                         term._coefficient == -1, "unsupported new tableau term" );
                fresh = term._variable;
                ++count;
            }
        require( count == 1 && introduced.insert( fresh ).second,
                 "expected one distinct new variable per equation" );
        if ( row ) out << ",";
        out << "\n    {\"equation\": " << row << ", \"variable\": " << fresh << "}";
        ++row;
    }
    out << "\n  ]\n}\n";
    out.close();
    require( bool( out ), "cannot write introduction list" );
}

// Independently serialize the processed query BEFORE solve(), without obtaining
// a header from a certificate. Query row order is Engine::createConstraintMatrix
// order; duplicate columns are rejected instead of silently choosing a value.
static void snapshot( const Query &query, const std::string &path,
                      CSRMatrix &matrix, Vector<double> &upper, Vector<double> &lower )
{
    unsigned n = query.getNumberOfVariables(), m = query.getNumberOfEquations();
    require( query.getNonlinearConstraints().empty(), "unsupported processed nonlinear constraint" );
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

// Record every ReLU whose phase is already fixed when solve() starts, with the
// valid split that Engine::solve will apply first (Engine.cpp 207-208). Its
// strictly tighter bounds become unexplained ground bounds (Engine::applySplit),
// so the importer must justify each phase exactly or reject the run.
static unsigned snapshot_phase_fixing( const Query &query, const std::string &path )
{
    std::ofstream out;
    unsigned fixed = 0;
    for ( const auto *constraint : query.getPiecewiseLinearConstraints() )
    {
        if ( !constraint->phaseFixed() ) continue;
        require( constraint->getType() == RELU && constraint->isActive(), "unexpected fixed constraint" );
        const auto *relu = static_cast<const ReluConstraint *>( constraint );
        require( relu->auxVariableInUse(), "fixed ReLU without auxiliary" );
        const PiecewiseLinearCaseSplit split = relu->getValidCaseSplit();
        require( split.getEquations().empty(), "unexpected valid-split equation" );
        if ( !fixed )
        {
            out.open( path );
            require( bool( out ), "cannot open phase-fixing record" );
            out << "{\n  \"format\": \"marabou-root-phase-fixing-v1\",\n  \"fixed\": [";
        }
        out << ( fixed ? ",\n    " : "\n    " ) << "{\"input\": " << relu->getB()
            << ", \"output\": " << relu->getF() << ", \"auxiliary\": " << relu->getAux()
            << ", \"phase\": \""
            << ( relu->getPhaseStatus() == RELU_PHASE_ACTIVE ? "active" : "inactive" )
            << "\", \"bounds\": [";
        bool first = true;
        for ( const auto &bound : split.getBoundTightenings() )
        {
            out << ( first ? "" : ", " ) << "{\"var\": " << bound._variable << ", \"type\": \""
                << ( bound._type == Tightening::LB ? "L" : "U" ) << "\", \"value\": ";
            write_number( out, bound._value );
            out << "}";
            first = false;
        }
        out << "]}";
        ++fixed;
    }
    if ( fixed )
    {
        out << "\n  ]\n}\n";
        out.close();
        require( bool( out ), "cannot write phase-fixing record" );
    }
    return fixed;
}

// Strict, untrusted reader for the marabou-exact-query-v1 text format
// (notes/EXACT_QUERY_FORMAT.md). Isabelle decodes the same bytes itself and
// checks that they denote the query captured below. Beyond the format, this
// pipeline needs numbers that are exactly binary doubles, so the solver sees
// them unchanged. Without native preprocessing it also needs equalities only
// and finite bounds for every variable; with it, le/ge statements become
// LE/GE equations for Preprocessor::makeAllEquationsEqualities and a missing
// bound stays infinite for the preprocessor to tighten.
static void reject( const std::string &message )
{
    throw std::runtime_error( "query file rejected: " + message );
}

static mpz_class parse_digits( const std::string &digits )
{
    if ( digits.empty() || digits.size() > 64 ||
         digits.find_first_not_of( "0123456789" ) != std::string::npos )
        reject( "malformed number or variable '" + digits + "'" );
    return mpz_class( digits, 10 );
}

static mpq_class parse_number( const std::string &token )
{
    bool negative = !token.empty() && token[0] == '-';
    std::string body = negative ? token.substr( 1 ) : token;
    mpq_class value;
    size_t slash = body.find( '/' ), dot = body.find( '.' );
    if ( slash != std::string::npos )
    {
        mpz_class denominator = parse_digits( body.substr( slash + 1 ) );
        if ( denominator == 0 ) reject( "zero denominator in '" + token + "'" );
        value = mpq_class( parse_digits( body.substr( 0, slash ) ), denominator );
    }
    else if ( dot != std::string::npos )
    {
        std::string fraction = body.substr( dot + 1 );
        mpz_class scale;
        mpz_ui_pow_ui( scale.get_mpz_t(), 10, fraction.size() );
        value = mpq_class( parse_digits( body.substr( 0, dot ) ) ) + mpq_class( parse_digits( fraction ), scale );
    }
    else
        value = mpq_class( parse_digits( body ) );
    value.canonicalize();
    return negative ? mpq_class( -value ) : value;
}

static double exact_double( const mpq_class &value, const std::string &token )
{
    double x = value.get_d();
    if ( !std::isfinite( x ) || mpq_class( x ) != value )
        reject( "number '" + token + "' is not exactly a binary double" );
    return x;
}

static unsigned parse_variable( const std::string &token, unsigned &variables )
{
    if ( token.size() < 2 || token[0] != 'x' ) reject( "malformed variable '" + token + "'" );
    mpz_class index = parse_digits( token.substr( 1 ) );
    if ( index >= 4096 ) reject( "variable index too large in '" + token + "'" );
    unsigned result = index.get_ui();
    variables = std::max( variables, result + 1 );
    return result;
}

static unsigned read_query_file( const std::string &path, InputQuery &input, bool preprocessing )
{
    std::ifstream in( path, std::ios::binary );
    require( bool( in ), "cannot open query file" );
    std::string data( ( std::istreambuf_iterator<char>( in ) ), std::istreambuf_iterator<char>() );
    if ( data.size() > 1000000 ) reject( "file too large" );
    std::vector<std::string> lines;
    size_t start = 0;
    for ( size_t i = 0; i < data.size(); ++i )
        if ( data[i] == '\n' )
        {
            lines.push_back( data.substr( start, i - start ) );
            start = i + 1;
        }
    if ( start != data.size() ) reject( "the last line must end with a newline" );
    if ( lines.empty() || lines[0] != "marabou-exact-query-v1" ) reject( "missing header line" );
    struct Row
    {
        std::vector<std::pair<std::string, unsigned>> terms;
        std::string scalar;
        Equation::EquationType type;
    };
    std::vector<Row> rows;
    std::map<unsigned, std::string> lower, upper;
    std::vector<std::pair<unsigned, unsigned>> relus;
    unsigned variables = 0;
    for ( size_t l = 1; l < lines.size(); ++l )
    {
        std::vector<std::string> tokens;
        size_t from = 0;
        const std::string &line = lines[l];
        for ( size_t i = 0; i <= line.size(); ++i )
            if ( i == line.size() || line[i] == ' ' )
            {
                if ( i == from ) reject( "empty token on line " + std::to_string( l + 1 ) );
                tokens.push_back( line.substr( from, i - from ) );
                from = i + 1;
            }
        const std::string &keyword = tokens[0];
        if ( ( keyword == "le" || keyword == "ge" ) && !preprocessing )
            reject( "le/ge statements are not supported by this capture pipeline" );
        if ( keyword == "eq" || keyword == "le" || keyword == "ge" )
        {
            const std::string relation = keyword == "eq" ? "=" : keyword == "le" ? "<=" : ">=";
            if ( tokens.size() < 3 || tokens[tokens.size() - 2] != relation || tokens.size() % 2 == 0 )
                reject( "malformed equation on line " + std::to_string( l + 1 ) );
            Row row;
            row.type = keyword == "eq" ? Equation::EQ : keyword == "le" ? Equation::LE : Equation::GE;
            std::set<unsigned> seen;
            for ( size_t i = 1; i + 2 < tokens.size(); i += 2 )
            {
                unsigned x = parse_variable( tokens[i + 1], variables );
                if ( !seen.insert( x ).second ) reject( "repeated variable in an equation" );
                row.terms.emplace_back( tokens[i], x );
            }
            row.scalar = tokens.back();
            rows.push_back( row );
        }
        else if ( keyword == "lower" || keyword == "upper" )
        {
            if ( tokens.size() != 3 ) reject( "malformed bound on line " + std::to_string( l + 1 ) );
            unsigned x = parse_variable( tokens[1], variables );
            auto &bounds = keyword == "lower" ? lower : upper;
            if ( !bounds.emplace( x, tokens[2] ).second )
                reject( "each variable needs exactly one lower and one upper bound" );
        }
        else if ( keyword == "relu" )
        {
            if ( tokens.size() != 3 ) reject( "malformed relu on line " + std::to_string( l + 1 ) );
            unsigned b = parse_variable( tokens[1], variables ), f = parse_variable( tokens[2], variables );
            if ( b == f ) reject( "a ReLU needs distinct input and output" );
            relus.emplace_back( b, f );
        }
        else
            reject( "unknown statement '" + keyword + "'" );
    }
    if ( rows.empty() )
        reject( preprocessing ? "at least one linear constraint is needed" : "at least one equation is needed" );
    input.setNumberOfVariables( variables );
    for ( unsigned x = 0; x < variables; ++x )
    {
        if ( !preprocessing && ( !lower.count( x ) || !upper.count( x ) ) )
            reject( "variable x" + std::to_string( x ) + " needs finite lower and upper bounds" );
        if ( lower.count( x ) )
            input.setLowerBound( x, exact_double( parse_number( lower[x] ), lower[x] ) );
        if ( upper.count( x ) )
            input.setUpperBound( x, exact_double( parse_number( upper[x] ), upper[x] ) );
    }
    for ( const auto &row : rows )
    {
        Equation equation( row.type );
        for ( const auto &term : row.terms )
            equation.addAddend( exact_double( parse_number( term.first ), term.first ), term.second );
        equation.setScalar( exact_double( parse_number( row.scalar ), row.scalar ) );
        input.addEquation( equation );
    }
    for ( const auto &relu : relus )
        input.addPiecewiseLinearConstraint( new ReluConstraint( relu.first, relu.second ) );
    return relus.size();
}

// Record Preprocessor's variable maps (Preprocessor.cpp 1013-1044). Variables
// are numbered as before elimination: the input's, then one slack per LE/GE
// equation in order (makeAllEquationsEqualities), then one auxiliary per ReLU
// in order (transformConstraintsIfNeeded). The importer and Isabelle check
// every claim that matters; this record only proposes the renaming.
static void snapshot_preprocessing( const InputQuery &input, const Preprocessor *preprocessor,
                                    const Query *preprocessed, const std::string &path )
{
    const unsigned n = input.getNumberOfVariables();
    std::unique_ptr<Query> copy( input.generateQuery() );
    unsigned slacks = 0;
    for ( const auto &equation : copy->getEquations() )
        slacks += equation._type != Equation::EQ;
    const unsigned relus = copy->getPiecewiseLinearConstraints().size();
    for ( const auto *constraint : copy->getPiecewiseLinearConstraints() )
        require( constraint->getType() == RELU, "only ReLU constraints are supported" );
    require( copy->getNonlinearConstraints().empty(), "unsupported nonlinear constraint" );
    const unsigned before = n + slacks + relus;
    std::ofstream out( path );
    require( bool( out ), "cannot open preprocessing record" );
    out << "{\n  \"format\": \"marabou-preprocessing-map-v1\",\n"
        << "  \"input_variables\": " << n << ",\n  \"slacks\": " << slacks
        << ",\n  \"relu_auxiliaries\": " << relus << ",\n  \"result\": ";
    if ( preprocessed == nullptr )
    {
        // Preprocessor::preprocess threw InfeasibleQueryException: no query, no map.
        out << "\"infeasible\"\n}\n";
        out.close();
        require( bool( out ), "cannot write preprocessing record" );
        return;
    }
    const unsigned after = preprocessed->getNumberOfVariables();
    out << "\"preprocessed\",\n  \"preprocessed_variables\": " << after << ",\n  \"variables\": [";
    std::vector<bool> used( after, false );
    for ( unsigned i = 0; i < before; ++i )
    {
        out << ( i ? ",\n    " : "\n    " ) << "{\"old\": " << i << ", ";
        if ( preprocessor->variableIsFixed( i ) )
        {
            out << "\"fixed\": ";
            write_number( out, preprocessor->getFixedValue( i ) );
        }
        else if ( preprocessor->variableIsMerged( i ) )
            out << "\"merged\": " << preprocessor->getMergedIndex( i );
        else
        {
            const unsigned j = preprocessor->getNewIndex( i );
            require( j < after && !used[j], "unexpected preprocessing variable layout" );
            used[j] = true;
            out << "\"new\": " << j;
        }
        out << "}";
    }
    for ( unsigned j = 0; j < after; ++j )
        require( used[j], "unexpected preprocessing variable layout" );
    out << "\n  ]\n}\n";
    out.close();
    require( bool( out ), "cannot write preprocessing record" );
}

static bool same_preprocessing( const Preprocessor &a, const Preprocessor &b, unsigned variables )
{
    for ( unsigned i = 0; i < variables; ++i )
    {
        if ( a.variableIsFixed( i ) != b.variableIsFixed( i ) ||
             a.variableIsMerged( i ) != b.variableIsMerged( i ) )
            return false;
        if ( a.variableIsFixed( i ) && a.getFixedValue( i ) != b.getFixedValue( i ) )
            return false;
        if ( a.variableIsMerged( i ) && a.getMergedIndex( i ) != b.getMergedIndex( i ) )
            return false;
        if ( !a.variableIsFixed( i ) && !a.variableIsMerged( i ) && a.getNewIndex( i ) != b.getNewIndex( i ) )
            return false;
    }
    return true;
}

static std::string count_word( unsigned n )
{
    return n == 1 ? "one" : n == 2 ? "two" : std::to_string( n );
}

int main( int argc, char **argv )
{
    try
    {
        require( argc == 2 || argc == 3 ||
                 ( argc == 4 && ( std::string( argv[2] ) == "file" || std::string( argv[2] ) == "file-preprocess" ) ),
                 "usage: marabou_solver_capture OUTPUT_DIRECTORY [linear|relu|relu_aux|relu_aux_active|relu_aux_inactive|relu_split|relu_intro|relu_sequence|relu_chain|relu_sat|file QUERY.mqx|file-preprocess QUERY.mqx]" );
        std::string directory = argv[1];
        std::string scenario = argc >= 3 ? argv[2] : "linear";
        require( scenario == "file" || scenario == "file-preprocess" || scenario == "linear" || scenario == "relu" ||
                 scenario == "relu_aux" || scenario == "relu_aux_active" ||
                 scenario == "relu_aux_inactive" ||
                 scenario == "relu_split" || scenario == "relu_intro" ||
                 scenario == "relu_sequence" || scenario == "relu_chain" ||
                 scenario == "relu_sat", "unknown scenario" );
        bool introScenario = scenario == "relu_intro";
        bool chainScenario = scenario == "relu_chain";
        bool satScenario = scenario == "relu_sat";
        bool sequenceScenario = scenario == "relu_sequence" || chainScenario || satScenario;
        bool reluScenario = scenario != "linear";
        bool auxiliaryScenario = scenario == "relu_aux" || scenario == "relu_aux_active" || introScenario;
        bool activeScenario = scenario == "relu_aux_active";
        bool inactiveScenario = scenario == "relu_aux_inactive";
        bool splitScenario = scenario == "relu_split";
        // file-preprocess runs Marabou's own Preprocessor inside processInputQuery.
        bool preprocessScenario = scenario == "file-preprocess";
        bool fileScenario = scenario == "file" || preprocessScenario;
        unsigned fileRelus = 0;
        std::string prefix = directory + "/solver_" + ( fileScenario ? std::string( "file" ) : scenario );
        Options::get()->setBool( Options::PRODUCE_PROOFS, true );
        Options::get()->setInt( Options::VERBOSITY, 0 );
        Options::get()->setString( Options::LP_SOLVER, "native" );
        Options::get()->setString( Options::SYMBOLIC_BOUND_TIGHTENING_TYPE, "none" );
        GlobalConfiguration::USE_DEEPSOI_LOCAL_SEARCH = false;
        if ( splitScenario )
            Options::get()->setInt( Options::CONSTRAINT_VIOLATION_THRESHOLD, 1 );

        // Initialization must succeed; UNSAT and its evidence must come from solve().
        InputQuery input;
        if ( fileScenario )
            fileRelus = read_query_file( argv[3], input, preprocessScenario );
        else if ( !reluScenario )
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
        else if ( satScenario )
        {
            // b=x0, f=x1, c=x2, g=x3, z=x4, w=x5, y=x6.
            // b=z>=1/2 forces f=b active; c=w<=-1/4 forces g=0; f+g=y<=1.
            // Satisfiable, e.g. b=f=z=y=1/2, c=w=-1/4, g=0.
            input.setNumberOfVariables( 7 );
            const double lower[] = { -2, 0, -2, 0, 0.5, -2, 0 };
            const double upper[] = { 2, 2, 2, 2, 2, -0.25, 1 };
            for ( unsigned i = 0; i < 7; ++i )
            {
                input.setLowerBound( i, lower[i] );
                input.setUpperBound( i, upper[i] );
            }
            for ( const auto &terms : {
                List<Equation::Addend>{ { 1, 0 }, { -1, 4 } },
                List<Equation::Addend>{ { 1, 2 }, { -1, 5 } },
                List<Equation::Addend>{ { 1, 1 }, { 1, 3 }, { -1, 6 } } } )
            {
                Equation equation;
                for ( const auto &term : terms ) equation.addAddend( term._coefficient, term._variable );
                equation.setScalar( 0 );
                input.addEquation( equation );
            }
            input.addPiecewiseLinearConstraint( new ReluConstraint( 0, 1 ) );
            input.addPiecewiseLinearConstraint( new ReluConstraint( 2, 3 ) );
        }
        else if ( sequenceScenario )
        {
            // b=x0, f=x1, c=x2, g=x3, z=x4, w=x5.
            // Sum variant: b=c=z<=-1/2; f+g=w>=1/4.
            // Chain variant: b=z<=-1/2; c=f-1/4; g=w>=1/4.
            // Both f=ReLU(b) and g=ReLU(c) are needed for UNSAT.
            input.setNumberOfVariables( 6 );
            const double lower[] = { -2, 0, -2, 0, -2, 0.25 };
            const double upper[] = { 2, 2, 2, 2, -0.5, 2 };
            for ( unsigned i = 0; i < 6; ++i )
            {
                input.setLowerBound( i, lower[i] );
                input.setUpperBound( i, upper[i] );
            }
            List<List<Equation::Addend>> rows = chainScenario
                ? List<List<Equation::Addend>>{
                    { { 1, 0 }, { -1, 4 } },
                    { { 1, 2 }, { -1, 1 } },
                    { { 1, 3 }, { -1, 5 } } }
                : List<List<Equation::Addend>>{
                    { { 1, 0 }, { -1, 4 } },
                    { { 1, 2 }, { -1, 4 } },
                    { { 1, 1 }, { 1, 3 }, { -1, 5 } } };
            unsigned row = 0;
            for ( const auto &terms : rows )
            {
                Equation equation;
                for ( const auto &term : terms ) equation.addAddend( term._coefficient, term._variable );
                equation.setScalar( chainScenario && row == 1 ? -0.25 : 0 );
                input.addEquation( equation );
                ++row;
            }
            input.addPiecewiseLinearConstraint( new ReluConstraint( 0, 1 ) );
            input.addPiecewiseLinearConstraint( new ReluConstraint( 2, 3 ) );
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
        else if ( inactiveScenario )
        {
            // aux=x0, b=x1, f=x2, w=x3, t=x4; aux=w>=1/4 and f=t>=1/4.
            // The linear relaxation allows f=aux=1/4, b=0; the ReLU does not.
            // BoundManager::propagateTightenings notifies in index order, so
            // the auxiliary's positive lower bound is seen before f's.
            input.setNumberOfVariables( 5 );
            const double lower[] = { 0, -2, 0, 0.25, 0.25 };
            const double upper[] = { 2, 2, 2, 2, 2 };
            for ( unsigned i = 0; i < 5; ++i )
            {
                input.setLowerBound( i, lower[i] );
                input.setUpperBound( i, upper[i] );
            }
            for ( const auto &terms : {
                List<Equation::Addend>{ { 1, 0 }, { -1, 3 } },
                List<Equation::Addend>{ { 1, 2 }, { -1, 4 } },
                List<Equation::Addend>{ { 1, 2 }, { -1, 1 }, { -1, 0 } } } )
            {
                Equation equation;
                for ( const auto &term : terms ) equation.addAddend( term._coefficient, term._variable );
                equation.setScalar( 0 );
                input.addEquation( equation );
            }
            input.addPiecewiseLinearConstraint( new ReluConstraint( String( "relu,2,1,0" ) ) );
        }
        else
        {
            // b=x0, f=x1, z=x2, w=x3, aux=x4.
            // The root b/f bounds leave the phase unknown. Negative variants
            // use b=z<=-1/2 and f=w>=1/4; the active variant uses b=z>=1/2
            // and aux=w>=1/4. All include f-b-aux=0 and f=ReLU(b).
            input.setNumberOfVariables( introScenario ? 4 : 5 );
            double lower[] = { -1, 0, -1, 0.25, 0 };
            double upper[] = { 2, 2, -0.5, 2, 1 };
            if ( scenario == "relu_aux" || introScenario )
            {
                lower[0] = lower[2] = -2;
                upper[4] = 2;
            }
            if ( activeScenario )
            {
                lower[2] = 0.5;
                upper[2] = upper[4] = 2;
            }
            for ( unsigned i = 0; i < input.getNumberOfVariables(); ++i )
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
            if ( auxiliaryScenario && !introScenario )
                rows.append( auxiliaryRow );
            for ( const auto &terms : rows )
            {
                Equation equation;
                for ( const auto &term : terms ) equation.addAddend( term._coefficient, term._variable );
                equation.setScalar( 0 );
                input.addEquation( equation );
            }
            input.addPiecewiseLinearConstraint( introScenario
                ? new ReluConstraint( 0, 1 ) : new ReluConstraint( String( "relu,1,0,4" ) ) );
        }

        // A file with ReLUs uses the native introduction sequence, as relu_sequence,
        // unless the native preprocessor introduces the auxiliaries itself.
        bool nativeSequence = sequenceScenario || ( fileScenario && !preprocessScenario && fileRelus > 0 );
        unsigned expectedRelus = fileScenario ? fileRelus : sequenceScenario ? 2 : reluScenario ? 1 : 0;
        unsigned introductions = fileScenario ? fileRelus : sequenceScenario ? 2 : introScenario ? 1 : 0;
        std::unique_ptr<Query> introducedInput;
        const IQuery *engineInput = &input;
        if ( introScenario || nativeSequence )
        {
            introducedInput.reset( input.generateQuery() );
            if ( nativeSequence )
                introduce_native_relu_aux_sequence( *introducedInput, prefix );
            else
                introduce_native_relu_aux( *introducedInput, prefix );
            engineInput = introducedInput.get();
        }
        unsigned sourceVariables = engineInput->getNumberOfVariables();
        unsigned sourceRows = engineInput->getNumberOfEquations();
        Preprocessor standalone;
        std::unique_ptr<Query> preprocessed;
        if ( preprocessScenario )
        {
            // A second, identical Preprocessor::preprocess call exposes the
            // query the engine preprocesses to (compared below through the
            // variable maps, and in HOL through the tableau steps).
            try
            {
                preprocessed = standalone.preprocess( input, GlobalConfiguration::PREPROCESSOR_ELIMINATE_VARIABLES );
            }
            catch ( const InfeasibleQueryException & )
            {
                // Native preprocessing refutes the query itself and produces no
                // proof. Confirm that the engine agrees, and record only that.
                snapshot_preprocessing( input, nullptr, nullptr, prefix + "_preprocessing.json" );
                Engine engine;
                engine.setRandomSeed( 1 );
                require( !engine.processInputQuery( input, true ) && engine.getExitCode() == Engine::UNSAT,
                         "the engine's preprocessing disagrees with the recorded infeasibility" );
                std::ofstream report( prefix + "_run.json" );
                report << "{\n"
                       << "  \"scenario\": \"" << scenario << "\",\n"
                       << "  \"proof_production\": true,\n"
                       << "  \"preprocessing\": true,\n"
                       << "  \"deepsoi\": false,\n"
                       << "  \"initialization_succeeded\": false,\n"
                       << "  \"preprocessing_found_unsat\": true,\n"
                       << "  \"exit_code\": \"UNSAT\",\n"
                       << "  \"seed\": 1,\n"
                       << "  \"input_variables\": " << input.getNumberOfVariables() << ",\n"
                       << "  \"input_rows\": " << input.getNumberOfEquations() << ",\n"
                       << "  \"relu_constraints\": " << fileRelus << ",\n"
                       << "  \"native_certificate\": null\n"
                       << "}\n";
                report.close();
                require( bool( report ), "cannot write run report" );
                std::cout << "Engine::processInputQuery(input, true): false; exit code UNSAT\n"
                          << "Preprocessor::preprocess threw InfeasibleQueryException; no native proof exists.\n"
                          << "Recorded the infeasibility for exact re-derivation.\n";
                return 0;
            }
            require( preprocessed->getNetworkLevelReasoner() == nullptr, "unexpected network-level reasoner" );
            snapshot_preprocessing( input, &standalone, preprocessed.get(), prefix + "_preprocessing.json" );
            sourceVariables = preprocessed->getNumberOfVariables();
            sourceRows = preprocessed->getNumberOfEquations();
            snapshot_source( *preprocessed, prefix + "_source.json" );
        }
        else
            snapshot_source( *engineInput, prefix + "_source.json" );
        Engine engine;
        engine.setRandomSeed( 1 );
        require( engine.shouldProduceProofs(), "proof production disabled" );
        bool initialized = false;
        try
        {
            initialized = engine.processInputQuery( *engineInput, preprocessScenario );
        }
        catch ( const InfeasibleQueryException & )
        {
        }
        require( initialized, "initialization found UNSAT before solve" );
        require( engine.preprocessingEnabled() == preprocessScenario, "unexpected preprocessing setting" );
        if ( preprocessScenario )
        {
            unsigned before = input.getNumberOfVariables() + fileRelus;
            const std::unique_ptr<Query> copy( input.generateQuery() );
            for ( const auto &equation : copy->getEquations() )
                before += equation._type != Equation::EQ;
            require( same_preprocessing( standalone, *engine.getPreprocessor(), before ),
                     "the engine's preprocessing differs from the recorded one" );
            expectedRelus = preprocessed->getPiecewiseLinearConstraints().size();
        }
        Query processed( *engine.getQuery() );
        require( processed.getPiecewiseLinearConstraints().size() == expectedRelus, "unexpected ReLU count" );
        // The fixed scenarios still require every phase to be open. A file run
        // records each fixed phase for the importer to justify exactly.
        unsigned fixedPhases = 0;
        if ( fileScenario )
            fixedPhases = snapshot_phase_fixing( *engine.getQuery(), prefix + "_phase_fixing.json" );
        else
            for ( const auto *constraint : processed.getPiecewiseLinearConstraints() )
                require( !constraint->phaseFixed(), "ReLU phase fixed before solving (uncertified initial phase fixing)" );
        const auto *initialRoot = engine.getUNSATCertificateRoot();
        require( initialRoot && initialRoot->getPLCLemmas().empty() &&
                 initialRoot->getChildren().empty() && !initialRoot->getContradiction(),
                 "unexpected proof evidence before solve" );
        CSRMatrix matrix;
        Vector<double> upper, lower;
        snapshot( processed, prefix + "_query.json", matrix, upper, lower );
        snapshot_steps( sourceVariables, sourceRows, processed, prefix + "_steps.json" );
        EngineState initial;
        engine.storeState( initial, TableauStateStorageLevel::STORE_ENTIRE_TABLEAU_STATE );
        const auto &tableau = initial._tableauState;
        require( tableau._n == processed.getNumberOfVariables() &&
                 tableau._m == processed.getNumberOfEquations(), "snapshot dimensions differ" );
        snapshot_initial_basis( tableau, sourceVariables, prefix + "_initial_basis.json" );
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
        if ( fileScenario && !sat )
            require( engine.getExitCode() == Engine::UNSAT, "solve returned neither SAT nor UNSAT within 10 seconds" );
        if ( satScenario || ( fileScenario && sat ) )
        {
            // Record the native doubles for every processed variable, both as a
            // round-trip decimal and as an exact hexadecimal float. They are
            // candidate witness data; only the exact HOL check decides.
            require( sat && engine.getExitCode() == Engine::SAT, "solve did not return SAT" );
            // With preprocessing, Engine::extractSolution maps the solution back
            // to the input's variables (Engine.cpp 1736-1784).
            Query solution( processed );
            std::unique_ptr<Query> inputSolution;
            if ( preprocessScenario )
            {
                inputSolution.reset( input.generateQuery() );
                engine.extractSolution( *inputSolution );
            }
            else
                engine.extractSolution( solution );
            const Query &reported = preprocessScenario ? *inputSolution : solution;
            std::ofstream out( prefix + "_assignment.json" );
            require( bool( out ), "cannot open assignment" );
            out << "{\n  \"format\": \"marabou-assignment-v1\",\n  \"variables\": "
                << reported.getNumberOfVariables() << ",\n  \"values\": [";
            for ( unsigned i = 0; i < reported.getNumberOfVariables(); ++i )
            {
                double value = reported.getSolutionValue( i );
                out << ( i ? ",\n    " : "\n    " ) << "{\"var\": " << i << ", \"value\": ";
                write_number( out, value );
                out << ", \"hex\": \"" << std::hexfloat << value << std::defaultfloat << "\"}";
            }
            out << "\n  ]\n}\n";
            out.close();
            require( bool( out ), "cannot write assignment" );
            const auto *statistics = engine.getStatistics();
            std::ofstream report( prefix + "_run.json" );
            report << "{\n"
                   << "  \"scenario\": \"" << scenario << "\",\n"
                   << "  \"proof_production\": true,\n"
                   << "  \"preprocessing\": " << ( preprocessScenario ? "true" : "false" ) << ",\n"
                   << "  \"deepsoi\": false,\n"
                   << "  \"initialization_succeeded\": true,\n"
                   << "  \"solve_return\": true,\n"
                   << "  \"exit_code\": \"SAT\",\n"
                   << "  \"timeout_seconds\": 10,\n"
                   << "  \"seed\": 1,\n"
                   << "  \"input_variables\": " << sourceVariables << ",\n"
                   << "  \"native_relu_introductions\": " << introductions << ",\n"
                   << "  \"variables_before_relu_introduction\": "
                   << ( nativeSequence ? std::to_string( input.getNumberOfVariables() ) : "null" ) << ",\n"
                   << "  \"snapshot_before_relu_introduction\": " << ( nativeSequence ? "true" : "false" ) << ",\n"
                   << "  \"source_rows\": " << sourceRows << ",\n"
                   << "  \"source_snapshot_before_initialization\": true,\n"
                   << "  \"introduction_list_before_solve\": true,\n"
                   << "  \"proposed_introductions\": " << sourceRows << ",\n"
                   << "  \"processed_variables\": " << processed.getNumberOfVariables() << ",\n"
                   << "  \"processed_rows\": " << processed.getNumberOfEquations() << ",\n"
                   << "  \"relu_constraints\": " << processed.getPiecewiseLinearConstraints().size() << ",\n"
                   << "  \"relu_phase_unfixed_before_solve\": " << ( expectedRelus ? ( fixedPhases ? "false" : "true" ) : "null" ) << ",\n"
                   << "  \"assignment_variables\": " << reported.getNumberOfVariables() << ",\n"
                   << "  \"search_splits\": "
                   << statistics->getUnsignedAttribute( Statistics::NUM_SPLITS ) << ",\n"
                   << "  \"main_loop_iterations\": "
                   << statistics->getLongAttribute( Statistics::NUM_MAIN_LOOP_ITERATIONS ) << ",\n"
                   << "  \"simplex_steps\": "
                   << statistics->getLongAttribute( Statistics::NUM_SIMPLEX_STEPS ) << ",\n"
                   << "  \"tableau_pivots\": "
                   << statistics->getLongAttribute( Statistics::NUM_TABLEAU_PIVOTS ) << ",\n"
                   << "  \"initial_snapshot_matches_tableau_and_ground_bounds\": true\n"
                   << "}\n";
            report.close();
            require( bool( report ), "cannot write run report" );
            std::cout << "Engine::processInputQuery(input, " << ( preprocessScenario ? "true" : "false" ) << "): true\n"
                      << "Engine::solve(10): true; exit code SAT\n"
                      << "Proof production: true; preprocessing: " << ( preprocessScenario ? "true" : "false" )
                      << "; DeepSoI: false\n"
                      << "Processed variables: " << processed.getNumberOfVariables()
                      << "; rows: " << processed.getNumberOfEquations() << "\n";
            if ( nativeSequence )
                std::cout << "Native ReluConstraint::transformToUseAuxVariables: " << count_word( introductions )
                          << " calls; " << input.getNumberOfVariables() << " -> " << sourceVariables << " variables.\n";
            if ( fixedPhases )
                std::cout << "ReLU phases fixed before solve: " << fixedPhases
                          << "; recorded with their valid splits.\n";
            if ( preprocessScenario )
                std::cout << "Native Preprocessor::preprocess: " << input.getNumberOfVariables() << " input -> "
                          << sourceVariables << " preprocessed variables; variable maps recorded.\n";
            std::cout << "Captured the native assignment of all " << reported.getNumberOfVariables()
                      << ( preprocessScenario ? " input" : " processed" )
                      << " variables; it is candidate witness data, not a proof.\n";
            return 0;
        }
        require( !sat && engine.getExitCode() == Engine::UNSAT, "solve did not return UNSAT" );
        const auto *root = engine.getUNSATCertificateRoot();
        require( root != nullptr, "solver produced no certificate" );
        require( root->getVisited() && !root->getSATSolutionFlag() &&
                 root->getDelegationStatus() == DONT_DELEGATE,
                 "expected a visited, nondelegated UNSAT node" );
        // Files may yield arbitrary trees and lemmas; the importer and Isabelle
        // check every node. The fixed scenarios also check their expected shape.
        if ( !fileScenario && splitScenario )
        {
            require( root->getChildren().size() == 2 && !root->getContradiction(),
                     "expected a binary native split" );
            require( root->getPLCLemmas().empty(), "unexpected root lemmas" );
            require( root->getSplit().getBoundTightenings().empty() &&
                     root->getSplit().getEquations().empty(), "unexpected root assumptions" );
            unsigned activeChildren = 0, inactiveChildren = 0;
            for ( const auto *child : root->getChildren() )
            {
                require( child && child->getVisited() && !child->getSATSolutionFlag() &&
                         child->getDelegationStatus() == DONT_DELEGATE &&
                         child->getChildren().empty() && child->getContradiction() &&
                         child->getPLCLemmas().empty(),
                         "expected two closed, nondelegated linear children" );
                const auto &split = child->getSplit();
                require( split.getEquations().empty() && split.getBoundTightenings().size() == 2,
                         "expected two native phase bounds" );
                bool bLower = false, bUpper = false, fUpper = false, aUpper = false;
                for ( const auto &bound : split.getBoundTightenings() )
                {
                    require( bound._value == 0, "unexpected phase bound value" );
                    bLower |= bound._variable == 0 && bound._type == Tightening::LB;
                    bUpper |= bound._variable == 0 && bound._type == Tightening::UB;
                    fUpper |= bound._variable == 1 && bound._type == Tightening::UB;
                    aUpper |= bound._variable == 2 && bound._type == Tightening::UB;
                }
                activeChildren += bLower && aUpper;
                inactiveChildren += bUpper && fUpper;
            }
            require( activeChildren == 1 && inactiveChildren == 1,
                     "expected exactly one active and one inactive child" );
        }
        else if ( !fileScenario )
            require( root->getChildren().empty() && root->getContradiction(),
                     "expected a closed leaf" );
        if ( fileScenario )
        {
        }
        else if ( !reluScenario )
            require( root->getPLCLemmas().empty(), "unexpected nonlinear evidence in linear case" );
        else if ( sequenceScenario )
            require( root->getPLCLemmas().size() >= 2, "expected evidence for both ReLUs" );
        else if ( inactiveScenario )
        {
            // Exactly the positive-auxiliary-lower rule: aux LB -> f UB zero.
            require( root->getPLCLemmas().size() == 1, "unexpected native ReLU lemma count" );
            const auto &lemma = root->getPLCLemmas().front();
            require( lemma && lemma->getConstraintType() == RELU &&
                     lemma->getCausingVars().size() == 1 && lemma->getCausingVars().front() == 0 &&
                     lemma->getCausingVarBound() == Tightening::LB &&
                     lemma->getAffectedVar() == 2 && lemma->getAffectedVarBound() == Tightening::UB &&
                     lemma->getBound() == 0 && lemma->getExplanations().size() == 1 &&
                     !lemma->getExplanations().front().empty(),
                     "unexpected positive-auxiliary ReLU propagation pattern" );
        }
        else if ( !splitScenario )
        {
            unsigned expected = ( scenario == "relu_aux" || introScenario ) ? 2 : 1;
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
        require( statistics->getUnsignedAttribute( Statistics::NUM_DELEGATED_LEAVES ) == 0,
                 "native proof has delegated leaves (unsupported evidence)" );
        require( fileScenario ||
                 statistics->getUnsignedAttribute( Statistics::NUM_CERTIFIED_LEAVES ) == ( splitScenario ? 2u : 1u ),
                 "unexpected explained leaf count" );
        if ( splitScenario )
            require( statistics->getUnsignedAttribute( Statistics::NUM_SPLITS ) == 1 &&
                     statistics->getUnsignedAttribute( Statistics::MAX_DECISION_LEVEL ) == 1,
                     "expected one native search split at depth one" );
        std::ofstream report( prefix + "_run.json" );
        report << "{\n"
               << "  \"scenario\": \"" << scenario << "\",\n"
               << "  \"proof_production\": true,\n"
               << "  \"preprocessing\": " << ( preprocessScenario ? "true" : "false" ) << ",\n"
               << "  \"deepsoi\": false,\n"
               << "  \"initialization_succeeded\": true,\n"
               << "  \"solve_return\": false,\n"
               << "  \"exit_code\": \"UNSAT\",\n"
               << "  \"timeout_seconds\": 10,\n"
               << "  \"seed\": 1,\n"
               << "  \"constraint_violation_threshold\": "
               << Options::get()->getInt( Options::CONSTRAINT_VIOLATION_THRESHOLD ) << ",\n"
               << "  \"input_variables\": " << sourceVariables << ",\n"
               << "  \"native_relu_introductions\": " << introductions << ",\n"
               << "  \"variables_before_relu_introduction\": "
               << ( introScenario || nativeSequence ? std::to_string( input.getNumberOfVariables() ) : "null" ) << ",\n"
               << "  \"snapshot_before_relu_introduction\": " << ( introScenario || nativeSequence ? "true" : "false" ) << ",\n"
               << "  \"source_rows\": " << sourceRows << ",\n"
               << "  \"source_snapshot_before_initialization\": true,\n"
               << "  \"introduction_list_before_solve\": true,\n"
               << "  \"proposed_introductions\": " << sourceRows << ",\n"
               << "  \"processed_variables\": " << processed.getNumberOfVariables() << ",\n"
               << "  \"processed_rows\": " << processed.getNumberOfEquations() << ",\n"
               << "  \"relu_constraints\": " << processed.getPiecewiseLinearConstraints().size() << ",\n"
               << "  \"relu_phase_unfixed_before_solve\": " << ( expectedRelus ? ( fixedPhases ? "false" : "true" ) : "null" ) << ",\n"
               << "  \"plc_lemmas_before_solve\": 0,\n"
               << "  \"plc_lemmas_after_solve\": " << root->getPLCLemmas().size() << ",\n"
               << "  \"root_children\": " << root->getChildren().size() << ",\n"
               << "  \"search_splits\": "
               << statistics->getUnsignedAttribute( Statistics::NUM_SPLITS ) << ",\n"
               << "  \"search_pops\": "
               << statistics->getUnsignedAttribute( Statistics::NUM_POPS ) << ",\n"
               << "  \"max_decision_level\": "
               << statistics->getUnsignedAttribute( Statistics::MAX_DECISION_LEVEL ) << ",\n"
               << "  \"main_loop_iterations\": "
               << statistics->getLongAttribute( Statistics::NUM_MAIN_LOOP_ITERATIONS ) << ",\n"
               << "  \"simplex_steps\": "
               << statistics->getLongAttribute( Statistics::NUM_SIMPLEX_STEPS ) << ",\n"
               << "  \"tableau_pivots\": "
               << statistics->getLongAttribute( Statistics::NUM_TABLEAU_PIVOTS ) << ",\n"
               << "  \"explicit_basis_tightening_calls\": "
               << statistics->getLongAttribute( Statistics::NUM_BOUND_TIGHTENINGS_ON_EXPLICIT_BASIS ) << ",\n"
               << "  \"explained_leaves\": "
               << statistics->getUnsignedAttribute( Statistics::NUM_CERTIFIED_LEAVES ) << ",\n"
               << "  \"delegated_leaves\": 0,\n"
               << "  \"initial_snapshot_matches_tableau_and_ground_bounds\": true\n"
               << "}\n";
        report.close();
        require( bool( report ), "cannot write run report" );
        std::cout << "Engine::processInputQuery(input, " << ( preprocessScenario ? "true" : "false" ) << "): true\n"
                  << "Engine::solve(10): false; exit code UNSAT\n"
                  << "Proof production: true; preprocessing: " << ( preprocessScenario ? "true" : "false" )
                  << "; DeepSoI: false\n"
                  << "Processed variables: " << processed.getNumberOfVariables()
                  << "; rows: " << processed.getNumberOfEquations() << "\n"
                  << "PLC lemmas: 0 before solve; " << root->getPLCLemmas().size() << " after solve\n"
                  << "Main-loop iterations: "
                  << engine.getStatistics()->getLongAttribute( Statistics::NUM_MAIN_LOOP_ITERATIONS )
                  << "; simplex steps: "
                  << engine.getStatistics()->getLongAttribute( Statistics::NUM_SIMPLEX_STEPS ) << "\n"
                  << "Initial query/tableau/ground-bound snapshot comparison: exact match\n"
                  << "Captured unmodified solver certificate and pre-solve query snapshot.\n"
                  << "Captured pre-initialization source query and " << sourceRows
                  << " proposed scalar-fixed introductions.\n";
        if ( introScenario )
            std::cout << "Native ReluConstraint::transformToUseAuxVariables: one call; "
                      << input.getNumberOfVariables() << " -> " << sourceVariables << " variables.\n"
                      << "Captured queries before and after the native ReLU introduction.\n";
        if ( nativeSequence )
            std::cout << "Native ReluConstraint::transformToUseAuxVariables: " << count_word( introductions ) << " calls; "
                      << input.getNumberOfVariables() << " -> " << sourceVariables << " variables.\n"
                      << "Captured queries before and after the native ReLU introduction sequence.\n";
        if ( fixedPhases )
            std::cout << "ReLU phases fixed before solve: " << fixedPhases
                      << "; recorded with their valid splits for exact justification.\n";
        if ( preprocessScenario )
            std::cout << "Native Preprocessor::preprocess: " << input.getNumberOfVariables() << " input -> "
                      << sourceVariables << " preprocessed variables; variable maps recorded.\n"
                      << "The source snapshot above is the preprocessed query.\n";
        if ( splitScenario )
            std::cout << "Binary ReLU split: one active and one inactive child, both closed.\n"
                      << "Search splits: " << statistics->getUnsignedAttribute( Statistics::NUM_SPLITS )
                      << "; tableau pivots: " << statistics->getLongAttribute( Statistics::NUM_TABLEAU_PIVOTS )
                      << "; explained leaves: " << statistics->getUnsignedAttribute( Statistics::NUM_CERTIFIED_LEAVES ) << "\n";
        return 0;
    }
    catch ( const std::exception &error )
    {
        std::cerr << "Capture failed: " << error.what() << "\n";
        return 1;
    }
}
