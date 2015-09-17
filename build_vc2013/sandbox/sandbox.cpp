#define LK_USE_WXWIDGETS 1

#include <wx/wx.h>
#include <wx/frame.h>
#include <wx/stc/stc.h>
#include <wx/webview.h>
#include <wx/statbmp.h>
#include <wx/numformatter.h>
#include <wx/grid.h>
#include <wx/zstream.h>
#include <wx/app.h>



#include <../lk_absyn.h>
#include <../lk_env.h>
#include <../lk_stdlib.h>
#include <../lk_eval.h>
#include <../lk_lex.h>
#include <../lk_invoke.h>
#include <../lk_parse.h>


namespace lk {

enum Opcode {
	ADD, SUB, MUL, DIV, LT, GT, LE, GE, NE, EQ, INC, DEC, OR, AND, NOT, NEG, EXP, PSH, POP, ARG,
	J, JF, JT, IDX, KEY, MAT, WAT, SET, GET, WR, RREF, NREF, CREF, FREF, CALL, TCALL, RET, SZ, KEYS, TYP, VEC, HASH,
	__InvalidOp };

struct { Opcode op; const char *name; } op_table[] = {
	{ ADD, "add" }, // impl
	{ SUB, "sub" }, // impl
	{ MUL, "mul" }, // impl
	{ DIV, "div" }, // impl
	{ LT, "lt" }, // impl
	{ GT, "gt" }, // impl
	{ LE, "le" }, // impl
	{ GE, "ge" }, // impl
	{ NE, "ne" }, // impl
	{ EQ, "eq" }, // impl
	{ INC, "inc" }, // impl
	{ DEC, "dec" }, // impl
	{ OR, "or" }, // impl
	{ AND, "and" }, // impl
	{ NOT, "not" }, // impl
	{ NEG, "neg" }, // impl
	{ EXP, "exp" }, // impl
	{ PSH, "psh" }, // impl
	{ POP, "pop" }, // impl
	{ ARG, "arg" },
	{ J, "j" }, // impl
	{ JF, "jf" }, // impl
	{ JT, "jt" }, // impl
	{ IDX, "idx" }, // impl
	{ KEY, "key" }, // impl
	{ MAT, "mat" }, // impl
	{ WAT, "wat" }, // impl
	{ SET, "set" }, // impl
	{ GET, "get" }, // impl
	{ WR, "wr" },
	{ RREF, "rref" },
	{ NREF, "nref" },
	{ CREF, "cref" },
	{ FREF, "fref" },
	{ CALL, "call" },
	{ TCALL, "tcall" },
	{ RET, "ret" },
	{ SZ, "sz" }, // impl
	{ KEYS, "keys" }, // impl
	{ TYP, "typ" },
	{ VEC, "vec" },
	{ HASH, "hash" },
	{ __InvalidOp, 0 } };

class vm
{
	size_t ip, sp;
	std::vector< vardata_t > stack;
	std::vector< unsigned int > program;
	std::vector< vardata_t > constants;
	std::vector< lk_string > identifiers;
	lk_string errStr;
public:
	vm( size_t ssize = 2048 )
	{
		ip = sp = 0;
		stack.resize( ssize, vardata_t() );
	}

	virtual ~vm()
	{
	}

	void load( const std::vector<unsigned int> &code,
		const std::vector<vardata_t> &cnstvals,
		const std::vector<lk_string> &ids )
	{

		ip = sp = 0;
		program = code;
		constants = cnstvals;
		identifiers = ids;
		stack.clear();
	}
	
	bool special_set( const lk_string &name, vardata_t &val )
	{
		throw error_t( "no defined mechanism to set special variable '" + name + "'" );
	}

	bool special_get( const lk_string &name, vardata_t &val )
	{
		throw error_t( "no defined mechanism to get special variable '" + name + "'" );
	}

	enum ExecMode { NORMAL, DEBUG, SINGLE };

#define CHECK_FOR_ARGS(n) if ( sp < n ) return error("stack [sp=%d] error, %d arguments required", sp, n );

	bool run( ExecMode mode = NORMAL )
	{
		vardata_t nullval;
		size_t nexecuted = 0;
		const size_t code_size = program.size();
		size_t next_ip = code_size;
		vardata_t *lhs, *rhs;
		try {
			while ( ip < code_size )
			{
				Opcode op = (Opcode)(unsigned char)program[ip];
				size_t arg = ( program[ip] >> 8 );
				
				next_ip = ip+1;
			
				rhs = ( sp >= 1 ) ? &stack[sp-1] : NULL;
				lhs = ( sp >= 2 ) ? &stack[sp-2] : NULL;

				vardata_t &rhs_deref( rhs ? rhs->deref() : nullval );
				vardata_t &lhs_deref( lhs ? lhs->deref() : nullval );
				vardata_t &result( lhs ? *lhs : *rhs );

				switch( op )
				{
				case ADD:
					CHECK_FOR_ARGS( 2 );
					if ( lhs_deref.type() == vardata_t::STRING || lhs_deref.type() == vardata_t::STRING )
						result.assign( lhs_deref.as_string() + rhs_deref.as_string() );
					else
						result.assign( lhs_deref.num() + rhs_deref.num() );
					sp--;
					break;
				case SUB:
					CHECK_FOR_ARGS( 2 );
					result.assign( lhs_deref.num() - rhs_deref.num() );
					sp--;
					break;
				case MUL:
					CHECK_FOR_ARGS( 2 );
					result.assign( lhs_deref.num() * rhs_deref.num() );
					sp--;
					break;
				case DIV:
					CHECK_FOR_ARGS( 2 );
					if ( rhs_deref.num() == 0.0 )
						result.assign( std::numeric_limits<double>::quiet_NaN() );
					else
						result.assign( lhs_deref.num() / rhs_deref.num() );
					sp--;
					break;
				case EXP:
					CHECK_FOR_ARGS( 2 );
					result.assign( ::pow( lhs_deref.num() , rhs_deref.num() ) );
					sp--;
					break;
				case LT:
					CHECK_FOR_ARGS( 2 );
					result.assign( lhs_deref.lessthan( rhs_deref ) ? 1.0 : 0.0 );
					sp--;
					break;
				case LE:
					CHECK_FOR_ARGS( 2 );
					result.assign( ( lhs_deref.lessthan( rhs_deref )
						|| lhs_deref.equals( rhs_deref ) ) ? 1.0 : 0.0 );
					sp--;
					break;
				case GT:
					CHECK_FOR_ARGS( 2 );
					result.assign( ( !lhs_deref.lessthan( rhs_deref )
						&& !lhs_deref.equals( rhs_deref ) )  ? 1.0 : 0.0  );
					sp--;
					break;
				case GE:
					CHECK_FOR_ARGS( 2 );
					result.assign( !( lhs_deref.lessthan( rhs_deref ))  ? 1.0 : 0.0  );
					sp--;
					break;
				case EQ:
					CHECK_FOR_ARGS( 2 );
					result.assign(  lhs_deref.equals( rhs_deref )  ? 1.0 : 0.0  );
					sp--;
					break;
				case NE:
					CHECK_FOR_ARGS( 2 );
					result.assign(  lhs_deref.equals( rhs_deref )  ? 0.0 : 1.0  );
					sp--;
					break;
				case OR:
					CHECK_FOR_ARGS( 2 );
					result.assign(  (((int)lhs_deref.num()) || ((int)rhs_deref.num() )) ? 1 : 0   );
					sp--;
					break;
				case AND:
					CHECK_FOR_ARGS( 2 );
					result.assign(  (((int)lhs_deref.num()) && ((int)rhs_deref.num() )) ? 1 : 0   );
					sp--;
					break;
				case INC:
					CHECK_FOR_ARGS( 1 );
					rhs_deref.assign( rhs_deref.num() + 1.0 );
					result.copy( rhs_deref );
					break;
				case DEC:
					CHECK_FOR_ARGS( 1 );
					rhs_deref.assign( rhs_deref.num() - 1.0 );
					result.copy( rhs_deref );
					break;
				case NOT:
					CHECK_FOR_ARGS( 1 );
					result.assign( ((int)rhs_deref.num()) ? 0 : 1 );
					break;
				case NEG:
					CHECK_FOR_ARGS( 1 );
					result.assign( 0.0 - rhs_deref.num() );
					break;
				case PSH:
					if ( sp >= stack.size() ) return error("stack overflow [sp=%d]", stack.size());
					if ( arg >= constants.size() ) return error( "invalid constant value address: %d\n", arg );
					stack[sp++].copy( constants[arg] );
					break;
				case POP:
					if ( sp > 0 ) sp--;
					break;
				case J:
					next_ip = arg;
					break;
				case JT:
					CHECK_FOR_ARGS( 1 );
					if ( rhs_deref.as_boolean() ) next_ip = arg;
					sp--;
					break;
				case JF:
					CHECK_FOR_ARGS( 1 );
					if ( !rhs_deref.as_boolean() ) next_ip = arg;
					sp--;
					break;
				case IDX:
					{
						CHECK_FOR_ARGS( 2 );
						size_t index = rhs_deref.as_unsigned();
						vardata_t &arr = lhs_deref;
						bool is_mutable = ( arg != 0 );
						if ( is_mutable &&
							( arr.type() != vardata_t::VECTOR
							|| arr.length() <= index ) )
							arr.resize( index + 1 );

						result.assign( arr.index(index) );
						sp--;
					}
					break;
				case KEY:
					{
						CHECK_FOR_ARGS( 2 );
						lk_string key( rhs_deref.as_string() );
						vardata_t &hash = lhs_deref;
						bool is_mutable = (arg != 0);
						if ( is_mutable && hash.type() != vardata_t::HASH )
							hash.empty_hash();

						vardata_t *x = hash.lookup( key );
						if ( !x ) hash.assign( key, x=new vardata_t );

						result.assign( x );
						sp--;
					}
					break;
				case MAT:
					CHECK_FOR_ARGS( 2 );
					if ( lhs_deref.type() == vardata_t::HASH )
					{
						lk::varhash_t *hh = lhs_deref.hash();
						lk::varhash_t::iterator it = hh->find( rhs_deref.as_string() );
						if ( it != hh->end() )
							hh->erase( it );
					}
					else if( lhs_deref.type() == vardata_t::VECTOR )
					{
						std::vector<lk::vardata_t> *vv = lhs_deref.vec();
						size_t idx = rhs_deref.as_unsigned();
						if ( idx < vv->size() )
							vv->erase( vv->begin() + idx );
					}
					else
						return error( "-@ requires a hash or vector" );

					sp--;
					break;

				case WAT:
					if ( lhs_deref.type() == vardata_t::HASH )
					{
						lk::varhash_t *hh = lhs_deref.hash();
						result.assign( hh->find( rhs_deref.as_string() ) != hh->end() ? 1.0 : 0.0 );
					}
					else if ( lhs_deref.type() == vardata_t::VECTOR )
					{
						result.assign( -1.0 );
						std::vector<lk::vardata_t> *vv = lhs_deref.vec();
						for( size_t i=0;i<vv->size();i++ )
						{
							if ( (*vv)[i].equals( rhs_deref ) )
							{
								result.assign( (double)i );
								break;
							}
						}
					}
					else if ( lhs_deref.type() == vardata_t::STRING )
					{
						lk_string::size_type pos = lhs_deref.str().find( rhs_deref.as_string() );
						result.assign( pos!=lk_string::npos ? (int)pos : -1.0 );
					}
					else
						return error("?@ requires a hash, vector, or string");
				
					sp--;
					break;

				case GET:
					if ( sp >= stack.size() ) return error("stack overflow [sp=%d]", stack.size());
					if ( arg >= identifiers.size() ) return error( "invalid identifier address: %d\n", arg );
					if ( !special_get( identifiers[arg], stack[sp++] ) )
						return error("failed to read external value '%s'", (const char*)identifiers[arg].c_str() );
					break;

				case SET:
					CHECK_FOR_ARGS( 1 );
					if ( arg >= identifiers.size() ) return error( "invalid identifier address: %d\n", arg );
					if ( !special_set( identifiers[arg], rhs_deref ) )
						return error("failed to write external value '%s'", (const char*)identifiers[arg].c_str() );
					sp--;
					break;
				case SZ:
					CHECK_FOR_ARGS( 1 );
					if (rhs_deref.type() == vardata_t::VECTOR)
						result.assign( (int) rhs_deref.length() );
					else if (rhs_deref.type() == vardata_t::STRING)
						result.assign( (int) rhs_deref.str().length() );
					else if (rhs_deref.type() == vardata_t::HASH)
					{
						int count = 0;

						varhash_t *h = rhs_deref.hash();
						for( varhash_t::iterator it = h->begin();
							it != h->end();
							++it )
						{
							if ( (*it).second->deref().type() != vardata_t::NULLVAL )
								count++;
						}
						result.assign( count );
					}
					else
						return error( "operand to sizeof must be a array, string, or table type");

					sp--;
					break;
				case KEYS:
					CHECK_FOR_ARGS( 1 );
					if (rhs_deref.type() == vardata_t::HASH)
					{
						varhash_t *h = rhs_deref.hash();
						result.empty_vector();
						result.vec()->reserve( h->size() );
						for( varhash_t::iterator it = h->begin();
							it != h->end();
							++it )
						{
							if ( (*it).second->deref().type() != vardata_t::NULLVAL )
								result.vec_append( (*it).first );
						}
						return true;
					}
					else
						return error( "operand to @ (keysof) must be a table");
					sp--;
					break;

				default:
					return error( "invalid instruction (0x%02X)", (unsigned int)op );
				};

				ip = next_ip;

				nexecuted++;
				if ( mode == SINGLE && nexecuted > 0 ) return true;
			}
		} catch( std::exception &exc ) {
			return error("runtime exception: %s", exc.what() );
		}

		return true;
	}

	lk_string error() { return errStr; }

	bool error( const char *fmt, ... )
	{
		char buf[512];
		va_list args;
		va_start( args, fmt );
		vsprintf( buf, fmt, args );
		va_end( args );
		errStr = buf;	
		return false;
	}
};

class code_gen
{
private:	
	struct instr {
		instr( Opcode _op, int _arg, const char *lbl = 0 )
			: op(_op), arg(_arg) {
			srcln = 0;
			label = 0;
			if ( lbl ) label = new lk_string(lbl);
		}
		instr( const instr &cpy )
		{
			copy( cpy );
		}
		~instr() { 
			if (label) delete label;
		}
		void copy( const instr &cpy )
		{
			srcln = cpy.srcln;
			op = cpy.op;
			arg = cpy.arg;
			label = 0;
			if ( cpy.label )
				label = new lk_string(*cpy.label);
		}

		instr &operator=( const instr &rhs ) {
			copy( rhs );
			return *this;
		}

		Opcode op;
		int arg;
		lk_string *label;
		int srcln;
	};

	node_t *m_currentNode;
	std::vector<instr> m_asm;
	typedef unordered_map< lk_string, int, lk_string_hash, lk_string_equal > LabelMap;
	LabelMap m_labelAddr;
	std::vector< vardata_t > m_constData;
	std::vector< lk_string > m_idList;
	int m_labelCounter;
	std::vector<lk_string> m_breakAddr, m_continueAddr;
	lk_string m_errStr;

	bool error( const char *fmt, ... )
	{
		char buf[512];
		va_list args;
		va_start( args, fmt );
		vsprintf( buf, fmt, args );
		va_end( args );
		m_errStr = buf;	
		return false;
	}

	// context flags for pfgen()
#define F_NONE 0x00
#define F_MUTABLE 0x01

public:
	code_gen() {
		m_labelCounter = 1;
		m_currentNode = 0;
	}
	
	lk_string error() { return m_errStr; }
	
	size_t bytecode( std::vector<unsigned int> &bc, 
		std::vector<vardata_t> &constData, 
		std::vector<lk_string> &idList )
	{
		if ( m_asm.size() == 0 ) return 0;

		bc.resize( m_asm.size(), 0 );

		for( size_t i=0;i<m_asm.size();i++ )
		{
			instr &ip = m_asm[i];
			if ( ip.label ) m_asm[i].arg = m_labelAddr[ *ip.label ];
			bc[i] = (((unsigned int)ip.op)&0x000000FF) | (((unsigned int)ip.arg)<<8);
		}

		constData = m_constData;
		idList = m_idList;

		return m_asm.size();
	}

	void output( lk_string &assembly, lk_string &bytecode )
	{
		char buf[128];		
		
		for( size_t i=0;i<m_asm.size();i++ )
		{
			instr &ip = m_asm[i];

			if ( ip.label )
				m_asm[i].arg = m_labelAddr[ *ip.label ];

			// determine if there's a label for this line (not super efficient)
			for( LabelMap::iterator it = m_labelAddr.begin();
				it != m_labelAddr.end();
				++it )
				if ( (int)i == it->second )
					assembly += it->first + ":\n";

			
			size_t j=0;
			while( op_table[j].name != 0 )
			{
				if ( ip.op == op_table[j].op )
				{
					sprintf( buf, "%4d  %4s ", ip.srcln, op_table[j].name );
					assembly += buf;

					if ( ip.label )
					{
						assembly += (*ip.label);
					}
					else if ( ip.op == PSH )
					{
						assembly += m_constData[ip.arg].as_string();
					}
					else if ( ip.op == SET || ip.op == GET || ip.op == RREF || ip.op == NREF || ip.op == CREF || ip.op == ARG )
					{
						assembly += m_idList[ip.arg];
					}
					else if ( ip.op == TCALL || ip.op == CALL || ip.op == VEC || ip.op == HASH )
					{
						sprintf(buf, "(%d)", ip.arg );
						assembly += buf;
					}

					assembly += '\n';

					unsigned int bc = (((unsigned int)ip.op)&0x000000FF) | (((unsigned int)ip.arg)<<8);
					sprintf(buf, "0x%08X\n", bc);
					bytecode += buf;
					break;
				}
				j++;
			}
		}
		
		for( size_t i=0;i<m_constData.size();i++ )
			bytecode += ".data " + m_constData[i].as_string() + "\n";

		for( size_t i=0;i<m_idList.size();i++ )
			bytecode += ".id " + m_idList[i] + "\n";
	}

	bool build( lk::node_t *root )
	{
		m_currentNode = 0;
		m_idList.clear();
		m_constData.clear();
		m_asm.clear();
		m_labelAddr.clear();
		m_labelCounter = 0;
		m_breakAddr.clear();
		m_continueAddr.clear();
		bool ok = pfgen(root, F_NONE );
		place_label( "HALT" );
		return ok;
	}

private:

	int place_identifier( const lk_string &id )
	{
		for( size_t i=0;i<m_idList.size();i++ )
			if ( m_idList[i] == id )
				return (int)i;

		m_idList.push_back( id );
		return m_idList.size() - 1;
	}

	int place_const( vardata_t &d )
	{
		if ( d.type() == vardata_t::HASH && d.hash()->size() == 2 )
			printf("stop here" );

		for( size_t i=0;i<m_constData.size();i++ )
			if ( m_constData[i].equals( d ) )
				return (int)i;

		m_constData.push_back( d );
		return (int)m_constData.size()-1;
	}

	int const_value( double value )
	{
		vardata_t x;
		x.assign( value );
		return place_const( x );
	}
	int const_literal( const lk_string &lit )
	{
		vardata_t x;
		x.assign( lit );
		return place_const( x );
	}

	lk_string new_label()
	{
		return lk::format( "L%d", m_labelCounter++ );
	}

	void place_label( const lk_string &s )
	{
		m_labelAddr[ s ] = (int)m_asm.size();
	}

	int emit( Opcode o, int arg = 0)
	{
		instr x( o, arg );
		x.srcln = m_currentNode ? m_currentNode->line() : 0;
		m_asm.push_back( x );
		return m_asm.size();
	}

	int emit( Opcode o, const lk_string &L )
	{
		instr x(o, 0, (const char*) L.c_str());
		x.srcln = m_currentNode ? m_currentNode->line() : 0;
		m_asm.push_back( x );
		return m_asm.size();
	}

	bool initialize_const_vec( lk::list_t *v, vardata_t &vvec )
	{
		while( v )
		{
			if ( lk::constant_t *cc = dynamic_cast<constant_t*>(v->item) )				
				vvec.vec_append( cc->value );
			else if ( lk::literal_t *cc = dynamic_cast<literal_t*>(v->item) )
				vvec.vec_append( cc->value );
			else if ( lk::expr_t *expr = dynamic_cast<expr_t*>(v->item) )
			{
				if ( expr->oper == expr_t::INITVEC )
				{
					lk::vardata_t subvec;
					subvec.empty_vector();
					if ( !initialize_const_vec( dynamic_cast<list_t*>(expr->left), subvec ) )
						return false;
					vvec.vec()->push_back( subvec );
				}
				else if ( expr->oper == expr_t::INITHASH )
				{
					lk::vardata_t subhash;
					subhash.empty_hash();
					if ( !initialize_const_hash( dynamic_cast<list_t*>(expr->left), subhash ) )
						return false;
					vvec.vec()->push_back( subhash );
				}
				else
					return false;
			}
			else
				return false;

			v = v->next;
		}

		return true;
	}

	bool initialize_const_hash( lk::list_t *v, vardata_t &vhash )
	{
		while( v )
		{
			expr_t *assign = dynamic_cast<expr_t*>(v->item);
			if (assign && assign->oper == expr_t::ASSIGN)
			{
				lk_string key;
				vardata_t val;
				if ( lk::literal_t *pkey = dynamic_cast<literal_t*>(assign->left) ) key = pkey->value;
				else return false;
				
				if ( lk::constant_t *cc = dynamic_cast<constant_t*>(assign->right) )				
					val.assign( cc->value );
				else if ( lk::literal_t *cc = dynamic_cast<literal_t*>(assign->right) )
					val.assign( cc->value );
				else if ( lk::expr_t *expr = dynamic_cast<expr_t*>(assign->right) )
				{
					if ( expr->oper == expr_t::INITVEC )
					{
						lk::vardata_t subvec;
						subvec.empty_vector();
						if ( !initialize_const_vec( dynamic_cast<list_t*>(expr->left), subvec ) )
							return false;
					}
					else if ( expr->oper == expr_t::INITHASH )
					{
						lk::vardata_t subhash;
						subhash.empty_hash();
						if ( !initialize_const_hash( dynamic_cast<list_t*>(expr->left), subhash ) )
							return false;
					}
					else
						return false;
				}

				vhash.hash_item(key).copy( val );
			}
			else
				return false;

			v = v->next;
		}

		return true;
	}


	bool pfgen( lk::node_t *root, unsigned int flags )
	{
		m_currentNode = root;
		if ( !root ) return true;

		if ( list_t *n = dynamic_cast<list_t*>( root ) )
		{
			while( n )
			{
				if ( !pfgen( n->item, flags ) )
					return false;

				n=n->next;
			}
		}
		else if ( iter_t *n = dynamic_cast<iter_t*>( root ) )
		{
			if ( n->init && !pfgen( n->init, flags ) ) return false;

			// labels for beginning and end of loop
			lk_string Lb = new_label();
			lk_string Le = new_label();
			
			m_continueAddr.push_back( Lb );
			m_breakAddr.push_back( Le );

			place_label( Lb ) ;

			if ( !pfgen( n->test, flags ) ) return false;

			emit( JF, Le );
			
			pfgen( n->block, flags );

			if ( n->adv && !pfgen( n->adv, flags ) ) return false;

			emit( J, Lb );
			place_label( Le );

			m_continueAddr.pop_back();
			m_breakAddr.pop_back();
		}
		else if ( cond_t *n = dynamic_cast<cond_t*>( root ) )
		{	
			lk_string L1 = new_label();
			lk_string L2 = L1;

			pfgen( n->test, flags );
			emit( JF, L1 );
			pfgen( n->on_true, flags );
			if ( n->on_false )
			{
				L2 = new_label();
				emit( J, L2 );
				place_label( L1 );
				pfgen( n->on_false, flags );
			}
			place_label( L2 );
		}
		else if ( expr_t *n = dynamic_cast<expr_t*>( root ) )
		{
			switch( n->oper )
			{
			case expr_t::PLUS:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( ADD );
				break;
			case expr_t::MINUS:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( SUB );
				break;
			case expr_t::MULT:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( MUL );
				break;
			case expr_t::DIV:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( DIV );
				break;
			case expr_t::LT:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( LT );
				break;
			case expr_t::GT:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( GT );
				break;
			case expr_t::LE:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( LE );
				break;
			case expr_t::GE:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( GE );
				break;
			case expr_t::NE:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( NE );
				break;
			case expr_t::EQ:
				pfgen( n->left, flags );
				pfgen( n->right, flags );
				emit( EQ );
				break;
			case expr_t::INCR:
				pfgen( n->left, flags );
				emit( INC );
				break;
			case expr_t::DECR:
				pfgen( n->right, flags );
				emit( DEC );
				break;
			case expr_t::LOGIOR:
			{
				lk_string Lsc = new_label();
				pfgen(n->left, flags );
				emit( PSH, const_value(0) );
				emit( NE );
				emit( JT, Lsc );
				pfgen(n->right, flags);
				emit( OR );
				place_label( Lsc );
			}
				break;
			case expr_t::LOGIAND:
			{
				lk_string Lsc = new_label();
				pfgen(n->left, flags );
				emit( PSH, const_value(0) );
				emit( EQ );
				emit( JT, Lsc );
				pfgen(n->right, flags );
				emit( OR );
				place_label( Lsc );
			}
				break;
			case expr_t::NOT:
				pfgen(n->left, flags);
				emit( NOT );
				break;
			case expr_t::NEG:
				pfgen(n->left, flags);
				emit( NEG );
				break;				
			case expr_t::EXP:
				pfgen(n->left, flags);
				pfgen(n->right, flags);
				emit( EXP );
				break;
			case expr_t::INDEX:
				pfgen(n->left, flags );
				pfgen(n->right, F_NONE);
				emit( IDX, flags&F_MUTABLE );
				break;
			case expr_t::HASH:
				pfgen(n->left, flags);
				pfgen(n->right, F_NONE);
				emit( KEY, flags&F_MUTABLE );
				break;
			case expr_t::MINUSAT:
				pfgen(n->left, F_NONE );
				pfgen(n->right, flags);
				emit( MAT );
				break;
			case expr_t::WHEREAT:
				pfgen(n->left, F_NONE );
				pfgen(n->right, flags);
				emit( WAT );
				break;
			case expr_t::PLUSEQ:
				pfgen(n->left, F_NONE);
				pfgen(n->right, F_NONE);
				emit( ADD );
				pfgen(n->left, F_NONE);
				emit( WR );
				break;
			case expr_t::MINUSEQ:
				pfgen(n->left, F_NONE);
				pfgen(n->right, F_NONE);
				emit( SUB );
				pfgen(n->left, F_NONE);
				emit( WR );
				break;
			case expr_t::MULTEQ:
				pfgen(n->left, F_NONE);
				pfgen(n->right, F_NONE);
				emit( MUL );
				pfgen(n->left, F_NONE);
				emit( WR );
				break;
			case expr_t::DIVEQ:
				pfgen(n->left, F_NONE);
				pfgen(n->right, F_NONE);
				emit( DIV );
				pfgen(n->left, F_NONE);
				emit( WR );
				break;
			case expr_t::ASSIGN:
				{
					if ( !pfgen( n->right, flags ) ) return false;

					bool sset = false;
					// if on the LHS of the assignment we have a special variable i.e. ${xy}, use a 
					// hack to assign the value to the storage location
					if ( lk::iden_t *iden = dynamic_cast<lk::iden_t*>(n->left) )
					{
						if ( iden->special )
						{
							emit( SET, place_identifier(iden->name) );
							return true;
						}
					}

					if ( !pfgen( n->left, F_MUTABLE ) ) return false;
					emit( WR );
				}
				break;
			case expr_t::CALL:
			case expr_t::THISCALL:
			{
				// evaluate all the arguments and pushon to stack
				list_t *argvals = dynamic_cast<list_t*>(n->right);
				list_t *p = argvals;
				int nargs = 0;
																
				while( p )
				{
					pfgen( p->item, F_NONE );
					p = p->next;
					nargs++;
				}

				pfgen( n->left, F_NONE );
				emit( (n->oper == expr_t::THISCALL)? TCALL : CALL, nargs );
			}
				break;
			case expr_t::SIZEOF:
				pfgen( n->left, F_NONE );
				emit( SZ );
				break;
			case expr_t::KEYSOF:
				pfgen( n->left, F_NONE );
				emit( KEYS );
				break;
			case expr_t::TYPEOF:
				pfgen( n->left, F_NONE );
				emit( TYP );
				break;
			case expr_t::INITVEC:
			{
				list_t *p = dynamic_cast<list_t*>( n->left );
				vardata_t cvec;
				cvec.empty_vector();
				if ( p && initialize_const_vec( p, cvec ) )
				{
					emit( PSH, place_const( cvec ) );
				}
				else
				{
					int len = 0;
					while( p )
					{
						pfgen( p->item, F_NONE );
						p = p->next;
						len++;
					}
					emit( VEC, len );
				}
			}
				break;
			case expr_t::INITHASH:
			{
				list_t *p = dynamic_cast<list_t*>( n->left );
				vardata_t chash;
				chash.empty_hash();
				if ( p && initialize_const_hash( p, chash ) )
				{
					emit( PSH, place_const( chash ) );
				}
				else
				{
					int npairs = 0;
					while (p)
					{
						expr_t *assign = dynamic_cast<expr_t*>(p->item);
						if (assign && assign->oper == expr_t::ASSIGN)
						{
							pfgen( assign->left, F_NONE );
							pfgen( assign->right, F_NONE );
						}
						p = p->next;
						npairs++;
					}
					emit( HASH, npairs );
				}
			}
				break;
			case expr_t::SWITCH:
			{
				lk_string Le( new_label() );
				std::vector<lk_string> labels;
				list_t *p = dynamic_cast<list_t*>( n->right );
				while( p )
				{
					labels.push_back( new_label() );
					p = p->next;
				}

				p = dynamic_cast<list_t*>( n->right );
				int idx = 0;
				while( p )
				{
					pfgen( n->left, F_NONE );
					emit( PSH,  const_value(idx) );
					emit( EQ );
					emit( JT, labels[idx] );
					p = p->next;
					idx++;
				}

				emit( J, Le );
				
				p = dynamic_cast<list_t*>( n->right );
				idx = 0;
				while( p )
				{
					place_label( labels[idx] );
					pfgen( p->item, F_NONE );
					emit( J, Le );
					p = p->next;
				}

				place_label( Le );
			}
				break;

			case expr_t::RETURN:
				pfgen(n->left, F_NONE );
				emit( RET );
				break;

			case expr_t::BREAK:
				if ( m_breakAddr.size() == 0 )
					return false;

				emit( J, m_breakAddr.back() );
				break;

			case expr_t::CONTINUE:
				if ( m_continueAddr.size() == 0 )
					return false;
				emit( J, m_continueAddr.back() );
				break;

			case expr_t::EXIT:
				emit( J,  "HALT" );
				break;

			case expr_t::DEFINE:
			{
				lk_string Le( new_label() );
				lk_string Lf( new_label() );
				emit( J, Le );
				place_label( Lf );

				list_t *p = dynamic_cast<list_t*>(n->left );
				int iarg = 0;
				while( p )
				{
					iden_t *id = dynamic_cast<iden_t*>( p->item );
					emit( ARG, place_identifier(id->name) );
					p = p->next;
				}

				pfgen( n->right, F_NONE );

				if ( m_asm.back().op != RET )
					emit( RET );

				place_label( Le );
				emit( FREF, Lf );

			}
				break;

			default:
				return false;
			}
		}
		else if ( iden_t *n = dynamic_cast<iden_t*>( root ) )
		{			
			if ( n->special )
			{
				emit( GET, place_identifier(n->name) );
				return true;
			}
			else
			{
				Opcode op = RREF;
				if ( n->common ) op = CREF;
				else if ( flags & F_MUTABLE ) op = NREF;

				emit( op, place_identifier(n->name) );
			}
		}
		else if ( constant_t *n = dynamic_cast<constant_t*>(root ) )
		{
			emit( PSH, const_value( n->value ) );
		}
		else if ( literal_t *n = dynamic_cast<literal_t*>(root ) )
		{
			emit( PSH, const_literal( n->value ) );
		}

		return true;
	}
};

}; // namespace lk

enum { ID_CODE = wxID_HIGHEST+149, ID_PARSE, ID_ASM, ID_BYTECODE, ID_OUTPUT };

class VMTestFrame : public wxFrame
{
	wxTextCtrl *m_code, *m_parse, *m_asm, *m_bytecode, *m_output;
public:
	VMTestFrame() : wxFrame( NULL, wxID_ANY, "LK-VM", wxDefaultPosition, wxSize(1200,900) )
	{
		wxFont font( 12, wxFONTFAMILY_MODERN, wxFONTSTYLE_NORMAL, wxFONTWEIGHT_NORMAL, false, "Consolas" );

		m_code = new wxTextCtrl( this, ID_CODE, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_code->SetFont( font );

		m_parse = new wxTextCtrl( this, ID_PARSE, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_parse->SetFont( font );
		m_parse->SetForegroundColour( *wxBLUE );

		m_asm = new wxTextCtrl( this, ID_ASM, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_asm->SetFont( font );
		m_asm->SetForegroundColour( "Forest green" );
		
		m_bytecode = new wxTextCtrl( this, ID_BYTECODE, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_bytecode->SetFont( font );
		m_bytecode->SetForegroundColour( "Maroon" );
		
		m_output = new wxTextCtrl( this, ID_OUTPUT, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_output->SetFont( font );
		m_output->SetForegroundColour( "Dark green" );

		wxBoxSizer *hsizer = new wxBoxSizer( wxHORIZONTAL );
		hsizer->Add( m_code, 2, wxALL|wxEXPAND, 0 );
		hsizer->Add( m_parse, 1, wxALL|wxEXPAND, 0 );
		hsizer->Add( m_asm, 2, wxALL|wxEXPAND, 0 );
		hsizer->Add( m_bytecode, 1, wxALL|wxEXPAND, 0 );

		wxBoxSizer *vsizer = new wxBoxSizer( wxVERTICAL );
		vsizer->Add( hsizer, 3, wxALL|wxEXPAND, 0 );
		vsizer->Add( m_output, 1, wxALL|wxEXPAND, 0 );
		SetSizer(vsizer);

		m_code->LoadFile( wxGetHomeDir() + "/.lk-vm-code" );
		ParseAndGenerateAssembly();
	}

	static void output_cb( lk::invoke_t &cxt )
	{
		LK_DOC("out", "output data", "none" );
		VMTestFrame *frm = (VMTestFrame*)cxt.user_data();
		frm->m_output->AppendText( cxt.arg(0).as_string() );
	}

	void ParseAndGenerateAssembly()
	{
		wxString output, assembly, bytecode;
		lk::input_string input( m_code->GetValue() );
		lk::parser parse( input );
		if ( lk::node_t *node = parse.script() )
		{
			if ( parse.error_count() == 0 )
			{
				lk::pretty_print( output, node, 0 );
				lk::code_gen cg;
				if ( cg.build( node ) ) cg.output( assembly, bytecode );
				else assembly = "error in assembly generation";
			}
			else
			{
				for( int i=0;i<parse.error_count();i++ )
					output += parse.error(i) + "\n";
			}

			/*
			lk::env_t env;
			env.register_funcs( lk::stdlib_basic() );
			env.register_funcs( lk::stdlib_string() );
			env.register_funcs( lk::stdlib_math() );
			env.register_funcs( lk::stdlib_wxui() );
			env.register_func( VMTestFrame::output_cb, this );

			m_output->Clear();
			lk::eval vm( node, &env );
			if ( !vm.run() )
			{
				for( int i=0;i<vm.error_count();i++ )
					m_output->AppendText( vm.get_error(i) );
			}*/

			delete node;
		}
		else
			output = "invalid parse: no nodes obtained";


		m_parse->ChangeValue( output );
		m_asm->ChangeValue( assembly );
		m_bytecode->ChangeValue( bytecode );

	}

	void OnClose( wxCloseEvent &evt )
	{
		m_code->SaveFile( wxGetHomeDir() + "/.lk-vm-code" );
		wxTheApp->ScheduleForDestruction( this );
	}

	void OnCommand( wxCommandEvent &evt )
	{
		if ( evt.GetId() == ID_CODE )
			ParseAndGenerateAssembly();
	}

	DECLARE_EVENT_TABLE()
};

BEGIN_EVENT_TABLE( VMTestFrame, wxFrame )
	EVT_CLOSE( VMTestFrame::OnClose )
	EVT_TEXT( ID_CODE, VMTestFrame::OnCommand )
END_EVENT_TABLE()


class VMTestApp : public wxApp
{
public:
	VMTestApp() { }

	virtual bool OnInit()
	{
		(new VMTestFrame())->Show();
		return true;
	}
};

IMPLEMENT_APP(VMTestApp);
