// Exercise pinned upstream proof components on hand-constructed queries.
// Explained fixtures call BoundExplainer and computeBound; none runs solve().
#include "BoundExplainer.h"
#include "CSRMatrix.h"
#include "JsonWriter.h"
#include "ReluConstraint.h"
#include "UnsatCertificateUtils.h"

#include <fstream>
#include <stdexcept>
#include <string>

class OutputFile : public IFile
{
    std::string _path;
    std::ofstream _stream;
public:
    explicit OutputFile( const std::string &path ) : _path( path ) {}
    void open( Mode ) override
    {
        _stream.open( _path );
        if ( !_stream ) throw std::runtime_error( "cannot open fixture output" );
    }
    void write( const String &s ) override { _stream << s.ascii(); }
    void close() override
    {
        _stream.close();
        if ( !_stream ) throw std::runtime_error( "cannot write fixture output" );
    }
    String readLine( char ) override { throw std::runtime_error( "output only" ); }
    void read( HeapData &, unsigned ) override { throw std::runtime_error( "output only" ); }
};

static void add_relu_children( UnsatCertificateNode &parent, ReluConstraint &relu,
                               unsigned rows, unsigned &id )
{
    auto *active = new UnsatCertificateNode(
        &parent, relu.getCaseSplit( RELU_PHASE_ACTIVE ), 1, ++id );
    auto *inactive = new UnsatCertificateNode(
        &parent, relu.getCaseSplit( RELU_PHASE_INACTIVE ), 1, ++id );
    active->setVisited();
    inactive->setVisited();
    Vector<double> weights( rows, 0 );
    weights[0] = -1;
    active->setContradiction( new Contradiction( weights ) );
    inactive->setContradiction( new Contradiction( unsigned( 1 ) ) );
}

static void add_upper_lemma( UnsatCertificateNode &node, unsigned b, unsigned f,
                             double inputUpper, unsigned id,
                             const SparseUnsortedList &explanation = SparseUnsortedList( 0 ) )
{
    // Match the PLCLemma arguments in ReluConstraint::notifyUpperBound and
    // BoundManager::addLemmaExplanationAndTightenBound. The caller supplies
    // either a computed row explanation or the default empty explanation.
    // An empty explanation
    // refers to the current ground upper bound, not an unproved new bound.
    Vector<SparseUnsortedList> explanations = { explanation };
    double outputUpper = FloatUtils::max( 0, inputUpper );
    double minTarget = inputUpper < 0
        ? FloatUtils::max( inputUpper, -GlobalConfiguration::LEMMA_CERTIFICATION_TOLERANCE )
        : inputUpper;
    auto lemma = std::make_shared<PLCLemma>( List<unsigned>{ b }, f, outputUpper,
        Tightening::UB, Tightening::UB, explanations, RELU, minTarget, id );
    node.addPLCLemma( lemma );
}

int main( int argc, char **argv )
{
    if ( argc != 2 ) return 2;
    std::string directory = argv[1];
    {
        // x0 = x1, x0 <= 1/4, x1 >= 1/2. Half of the tableau row
        // has maximum 1/8 - 1/4 = -1/8 over these bounds.
        Vector<double> rows = { 1, -1 };
        CSRMatrix matrix;
        matrix.initialize( rows.data(), 1, 2 );
        UnsatCertificateNode root( nullptr, PiecewiseLinearCaseSplit(), 0, 0 );
        root.setVisited();
        root.setContradiction( new Contradiction( Vector<double>{ 0.5 } ) );
        OutputFile file( directory + "/linear.json" );
        JsonWriter::writeProofToJson( &root, 1, &matrix, { 0.25, 2 }, { -2, 0.5 }, {}, file );
    }
    for ( bool nested : { false, true } )
    {
        // Serialized ReLU order is f,b,aux. Writer order is b,f,aux,tableauAux.
        ReluConstraint first( String( "relu,1,0,2" ) );
        first.addTableauAuxVar( 3, 2 );
        ReluConstraint second( String( "relu,5,4,6" ) );
        second.addTableauAuxVar( 7, 6 );
        Vector<double> rows = nested
            ? Vector<double>{ -1, 1, -1, -1, 0, 0, 0, 0,
                               0, 0, 0, 0, -1, 1, -1, -1 }
            : Vector<double>{ -1, 1, -1, -1 };
        Vector<double> upper = nested ? Vector<double>{ 0, 2, 3, 0, 1, 1, 2, 0 }
                                      : Vector<double>{ 0, 2, 3, 0 };
        Vector<double> lower = nested ? Vector<double>{ -1, 1, 0, 0, -1, 0, 0, 0 }
                                      : Vector<double>{ -1, 1, 0, 0 };
        unsigned m = nested ? 2 : 1;
        CSRMatrix matrix;
        matrix.initialize( rows.data(), m, upper.size() );
        UnsatCertificateNode root( nullptr, PiecewiseLinearCaseSplit(), 0, 0 );
        root.setVisited();
        unsigned id = 0;
        List<PiecewiseLinearConstraint *> constraints = { &first };
        if ( nested )
        {
            constraints.append( &second );
            for ( auto phase : { RELU_PHASE_ACTIVE, RELU_PHASE_INACTIVE } )
            {
                auto *child = new UnsatCertificateNode(
                    &root, second.getCaseSplit( phase ), 0, ++id );
                child->setVisited();
                add_relu_children( *child, first, m, id );
            }
        }
        else add_relu_children( root, first, m, id );
        OutputFile file( directory + ( nested ? "/nested.json" : "/relu.json" ) );
        JsonWriter::writeProofToJson( &root, m, &matrix, upper, lower, constraints, file );
    }
    for ( double inputUpper : { -0.5, 0.5 } )
    {
        ReluConstraint relu( String( "relu,1,0,2" ) );
        relu.addTableauAuxVar( 3, 2 );
        Vector<double> rows = { -1, 1, -1, -1 };
        CSRMatrix matrix;
        matrix.initialize( rows.data(), 1, 4 );
        UnsatCertificateNode root( nullptr, PiecewiseLinearCaseSplit(), 0, 0 );
        root.setVisited();
        add_upper_lemma( root, 0, 1, inputUpper, 1 );
        root.setContradiction( new Contradiction( unsigned( 1 ) ) );
        OutputFile file( directory + ( inputUpper < 0 ? "/propagation.json"
                                                      : "/propagation_positive.json" ) );
        JsonWriter::writeProofToJson( &root, 1, &matrix,
            { inputUpper, 2, 3, 0 }, { -1, inputUpper < 0 ? 0.25 : 0.75, 0, 0 }, { &relu }, file );
    }
    for ( double zUpper : { 0.0, 0.5 } )
    {
        // Original rows: -b + f - aux - t = 0, b - 2*z + p - s = 0.
        // Last m variables t,s are tableau slacks. Explain b = 2*z - p + s.
        // All operands are dyadic: z <= zUpper, p >= 1/2, s = 0 give
        // b <= -1/2 or 1/2. The root's b <= 2 cannot justify the PLC claim.
        ReluConstraint relu( String( "relu,1,0,2" ) );
        relu.addTableauAuxVar( 5, 2 );
        Vector<double> rows = { -1, 1, -1, 0, 0, -1, 0,
                                1, 0, 0, -2, 1, 0, -1 };
        Vector<double> upper = { 2, 2, 4, zUpper, 2, 0, 0 };
        Vector<double> lower = { -2, zUpper == 0 ? 0.25 : 0.75, 0, -1, 0.5, 0, 0 };
        CSRMatrix matrix;
        matrix.initialize( rows.data(), 2, 7 );
        CVC4::context::Context context;
        BoundExplainer explainer( 7, 2, context );
        TableauRow row( 3 );
        row._scalar = 0;
        row._lhs = 0;
        row._row[0] = TableauRow::Entry( 3, 2 );
        row._row[1] = TableauRow::Entry( 4, -1 );
        row._row[2] = TableauRow::Entry( 6, 1 );
        explainer.updateBoundExplanation( row, true );
        const auto &explanation = explainer.getExplanation( 0, true );
        if ( explanation.empty() || explanation.get( 0 ) != 0 || explanation.get( 1 ) != -1 )
            throw std::runtime_error( "unexpected native bound explanation" );
        double inputUpper = UNSATCertificateUtils::computeBound(
            0, true, explanation, &matrix, upper.data(), lower.data(), 7 );
        if ( inputUpper != 2 * zUpper - 0.5 )
            throw std::runtime_error( "unexpected native explained upper bound" );
        UnsatCertificateNode root( nullptr, PiecewiseLinearCaseSplit(), 0, 0 );
        root.setVisited();
        add_upper_lemma( root, 0, 1, inputUpper, 1, explanation );
        root.setContradiction( new Contradiction( unsigned( 1 ) ) );
        OutputFile file( directory + ( zUpper == 0 ? "/explained_negative.json"
                                                   : "/explained_positive.json" ) );
        JsonWriter::writeProofToJson( &root, 2, &matrix, upper, lower, { &relu }, file );
    }
    {
        ReluConstraint first( String( "relu,1,0,2" ) );
        first.addTableauAuxVar( 3, 2 );
        ReluConstraint second( String( "relu,4,1,5" ) );
        second.addTableauAuxVar( 6, 5 );
        Vector<double> rows = { -1, 1, -1, -1, 0, 0, 0,
                                0, -1, 0, 0, 1, -1, -1 };
        CSRMatrix matrix;
        matrix.initialize( rows.data(), 2, 7 );
        UnsatCertificateNode root( nullptr, PiecewiseLinearCaseSplit(), 0, 0 );
        root.setVisited();
        add_upper_lemma( root, 0, 1, 0.5, 1 );
        add_upper_lemma( root, 1, 4, 0.5, 2 );
        root.setContradiction( new Contradiction( unsigned( 4 ) ) );
        OutputFile file( directory + "/propagation_chain.json" );
        JsonWriter::writeProofToJson( &root, 2, &matrix,
            { 0.5, 2, 3, 0, 2, 3, 0 }, { -1, 0, 0, 0, 0.75, 0, 0 }, { &first, &second }, file );
    }
    {
        ReluConstraint first( String( "relu,1,0,2" ) );
        first.addTableauAuxVar( 3, 2 );
        ReluConstraint second( String( "relu,5,4,6" ) );
        second.addTableauAuxVar( 7, 6 );
        Vector<double> rows = { -1, 1, -1, -1, 0, 0, 0, 0,
                                0, 0, 0, 0, -1, 1, -1, -1 };
        CSRMatrix matrix;
        matrix.initialize( rows.data(), 2, 8 );
        UnsatCertificateNode root( nullptr, PiecewiseLinearCaseSplit(), 0, 0 );
        root.setVisited();
        unsigned id = 0;
        for ( auto phase : { RELU_PHASE_ACTIVE, RELU_PHASE_INACTIVE } )
        {
            auto *child = new UnsatCertificateNode( &root, second.getCaseSplit( phase ), 0, ++id );
            child->setVisited();
            add_upper_lemma( *child, 0, 1, 0, id );
            child->setContradiction( new Contradiction( unsigned( 1 ) ) );
        }
        OutputFile file( directory + "/propagation_tree.json" );
        JsonWriter::writeProofToJson( &root, 2, &matrix,
            { 0, 2, 3, 0, 1, 1, 2, 0 }, { -1, 1, 0, 0, -1, 0, 0, 0 }, { &first, &second }, file );
    }
}
