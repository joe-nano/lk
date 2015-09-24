#include <algorithm>

#define LK_USE_WXWIDGETS 1

#include <wx/wx.h>
#include <wx/frame.h>
#include <wx/stc/stc.h>
#include <wx/webview.h>
#include <wx/statbmp.h>
#include <wx/numformatter.h>
#include <wx/tokenzr.h>
#include <wx/grid.h>
#include <wx/zstream.h>
#include <wx/app.h>
#include <wx/busyinfo.h>
#include <wx/stc/stc.h>

#include <../lk_absyn.h>
#include <../lk_env.h>
#include <../lk_stdlib.h>
#include <../lk_eval.h>
#include <../lk_lex.h>
#include <../lk_invoke.h>
#include <../lk_parse.h>

#include "mtrand.h"


namespace lk {

enum Opcode {
	ADD, SUB, MUL, DIV, LT, GT, LE, GE, NE, EQ, INC, DEC, OR, AND, NOT, NEG, EXP, PSH, POP, DUP, NUL, ARG,
	J, JF, JT, IDX, KEY, MAT, WAT, SET, GET, WR, RREF, NREF, CREF, FREF, CALL, TCALL, RET, END, SZ, KEYS, TYP, VEC, HASH,
	__MaxOp };

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
	{ NUL, "nul" }, // impl
	{ DUP, "dup", }, // impl
	{ ARG, "arg" }, // impl
	{ J, "j" }, // impl
	{ JF, "jf" }, // impl
	{ JT, "jt" }, // impl
	{ IDX, "idx" }, // impl
	{ KEY, "key" }, // impl
	{ MAT, "mat" }, // impl
	{ WAT, "wat" }, // impl
	{ SET, "set" }, // impl
	{ GET, "get" }, // impl
	{ WR, "wr" }, // impl
	{ RREF, "rref" }, // impl
	{ NREF, "nref" }, // impl
	{ CREF, "cref" }, // impl
	{ FREF, "fref" }, // impl
	{ CALL, "call" }, // impl
	{ TCALL, "tcall" }, // impl
	{ RET, "ret" }, // impl
	{ END, "end" }, // impl
	{ SZ, "sz" }, // impl
	{ KEYS, "keys" }, // impl
	{ TYP, "typ" }, // impl
	{ VEC, "vec" },
	{ HASH, "hash" },
	{ __MaxOp, 0 } };

#define OP_PROFILE 1 

class vm
{
public:
	struct frame {
		frame( lk::env_t *parent, size_t fptr, size_t ret, size_t na )
			: env( parent), fp(fptr), retaddr(ret), nargs(na), iarg(0), thiscall( false )
		{
		}

		lk::env_t env;
		size_t fp;
		size_t retaddr;
		size_t nargs;
		size_t iarg;
		bool thiscall;
	};

private:
	size_t ip, sp;
	std::vector< vardata_t > stack;
	std::vector< unsigned int > program;
	std::vector< vardata_t > constants;
	std::vector< lk_string > identifiers;
	std::vector< srcpos_t > debuginfo;
	std::vector< bool > brkpoints;
	std::vector< frame* > frames;
	lk_string errStr;

#ifdef OP_PROFILE
	size_t opcount[__MaxOp];
	void clear_opcount() {
		for( size_t i=0;i<__MaxOp;i++ )
			opcount[i] = 0;
	}
#endif

public:
	vm( size_t ssize = 2048 )
	{
		ip = sp = 0;
		stack.resize( ssize, vardata_t() );
		frames.reserve( 16 );

#ifdef OP_PROFILE
		clear_opcount();
#endif

	}

#ifdef OP_PROFILE
	void get_opcount( size_t iop[__MaxOp] )
	{
		for( size_t i=0;i<__MaxOp;i++ )
			iop[i] = opcount[i];
	}
#endif

	virtual ~vm()
	{
		for( size_t i=0;i<frames.size(); i++ )
			delete frames[i];
	}

	size_t get_ip() { return ip; }

	frame **get_frames( size_t *nfrm ) {
		*nfrm = frames.size();
		if ( frames.size() > 0 ) return &frames[0];
		else return 0;
	}

	vardata_t *get_stack( size_t *psp ) {
		*psp = sp;
		return &stack[0];
	}

	void load( const std::vector<unsigned int> &code,
		const std::vector<vardata_t> &cnstvals,
		const std::vector<lk_string> &ids,
		const std::vector<lk::srcpos_t> &dbginf)
	{
		program = code;
		constants = cnstvals;
		identifiers = ids;
		debuginfo = dbginf;

		restart();
	}
	
	bool special_set( const lk_string &name, vardata_t &val )
	{
		throw error_t( "no defined mechanism to set special variable '" + name + "'" );
	}

	bool special_get( const lk_string &name, vardata_t &val )
	{
		throw error_t( "no defined mechanism to get special variable '" + name + "'" );
	}

	void restart()
	{
#ifdef OP_PROFILE
		clear_opcount();
#endif

		errStr.clear();
		ip = sp = 0;
		for( size_t i=0;i<stack.size();i++ )
			stack[i].nullify();

		for( size_t i=0;i<frames.size();i++ )
			delete frames[i];
		frames.clear();

		brkpoints.clear();
		brkpoints.resize( program.size(), false );
	}

	enum ExecMode { NORMAL, DEBUG, SINGLE };

#define CHECK_FOR_ARGS(n) if ( sp < n ) return error("stack [sp=%d] error, %d arguments required", sp, n );
#define CHECK_OVERFLOW() if ( sp >= stack.size() ) return error("stack overflow [sp=%d]", stack.size())
#define CHECK_CONSTANT() if ( arg >= constants.size() ) return error( "invalid constant value address: %d\n", arg )
#define CHECK_IDENTIFIER() if ( arg >= identifiers.size() ) return error( "invalid identifier address: %d\n", arg )


	bool run( ExecMode mode = NORMAL, lk::env_t *env = 0 )
	{
		if ( frames.size() == 0 )
			frames.push_back( new frame( env, 0, 0, 0 ) );

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

#ifdef OP_PROFILE
				opcount[op]++;
#endif

				
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
					if ( lhs_deref.type() == vardata_t::STRING || rhs_deref.type() == vardata_t::STRING )
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
					//result.copy( *rhs );
					break;
				case DEC:
					CHECK_FOR_ARGS( 1 );
					rhs_deref.assign( rhs_deref.num() - 1.0 );
					//result.copy( *rhs );
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
					CHECK_OVERFLOW();
					CHECK_CONSTANT();
					stack[sp++].copy( constants[arg] );
					break;
				case POP:
					if ( sp == 0 ) return error("stack corruption at level 0");
					sp--;
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
					CHECK_OVERFLOW();
					CHECK_IDENTIFIER();
					if ( !special_get( identifiers[arg], stack[sp++] ) )
						return error("failed to read external value '%s'", (const char*)identifiers[arg].c_str() );
					break;

				case SET:
					CHECK_FOR_ARGS( 1 );
					CHECK_IDENTIFIER();
					if ( !special_set( identifiers[arg], rhs_deref ) )
						return error("failed to write external value '%s'", (const char*)identifiers[arg].c_str() );
					sp--;
					break;
				case SZ:
					CHECK_FOR_ARGS( 1 );
					if (rhs_deref.type() == vardata_t::VECTOR)
						rhs->assign( (int) rhs_deref.length() );
					else if (rhs_deref.type() == vardata_t::STRING)
						rhs->assign( (int) rhs_deref.str().length() );
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
						rhs->assign( count );
					}
					else
						return error( "operand to sizeof must be a array, string, or table type");

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
				case WR:
					CHECK_FOR_ARGS( 2 );
					rhs_deref.copy( lhs_deref );
					sp--;
					break;

				case RREF:
				case CREF:
				case NREF:
				{
					frame &F = *frames.back();
					CHECK_OVERFLOW();
					CHECK_IDENTIFIER();

					if ( fcallinfo_t *fci = F.env.lookup_func( identifiers[arg] ) )
					{
						stack[sp++].assign_fcall( fci );
					}
					else if ( vardata_t *x = F.env.lookup( identifiers[arg], op == RREF ) )
					{
						stack[sp++].assign( x );
					}
					else if ( op == CREF || op == NREF )
					{
						vardata_t *x = new vardata_t;
						if ( op == CREF )
						{
							x->set_flag( vardata_t::CONSTVAL );
							x->clear_flag( vardata_t::ASSIGNED );
						}
						F.env.assign( identifiers[arg], x );
						stack[sp++].assign( x );
					}
					else
						return error("referencing unassigned variable: %s\n", (const char*)identifiers[arg].c_str() );

					break;
				}

				case TYP:
					CHECK_OVERFLOW();
					CHECK_IDENTIFIER();

					if ( vardata_t *x = frames.back()->env.lookup( identifiers[arg], true ) )
						stack[sp++].assign( x->typestr() );
					else
						stack[sp++].assign( "unknown" );
					break;

				case FREF:
					CHECK_OVERFLOW();
					stack[sp++].assign_faddr( arg );
					break;
				
				case CALL:
				case TCALL:
				{
					CHECK_FOR_ARGS( arg+2 );
					if ( vardata_t::EXTFUNC == rhs_deref.type() && op == CALL )
					{
						frame &F = *frames.back();
						fcallinfo_t *fci = rhs_deref.fcall();
						vardata_t &retval = stack[ sp - arg - 2 ];
						invoke_t cxt( &F.env, retval, fci->user_data );

						for( size_t i=0;i<arg;i++ )
							cxt.arg_list().push_back( stack[sp-arg-1+i] );						
							
						try {
							if ( fci->f ) (*(fci->f))( cxt );
							else if ( fci->f_ext ) lk::external_call( fci->f_ext, cxt );
							else cxt.error( "invalid internal reference to function" );

							sp -= (arg+1); // leave return value on stack (even if null)
						}
						catch( std::exception &e )
						{
							return error( e.what() );
						}
					}
					else if ( vardata_t::INTFUNC == rhs_deref.type() )
					{
						frames.push_back( new frame( &frames.back()->env, sp, next_ip, arg ) );
						frame &F = *frames.back();
												
						vardata_t *__args = new vardata_t;
						__args->empty_vector();

						size_t offset = 1;						
						if ( op == TCALL )
						{
							offset = 2;
							F.env.assign( "this", new vardata_t( stack[sp-2] ) );
							F.thiscall = true;
						}

						for( size_t i=0;i<arg;i++ )
							__args->vec()->push_back( stack[sp-arg-offset+i] );		
						
						F.env.assign( "__args", __args );

						next_ip = rhs_deref.faddr(); 
					}
					else
						return error("invalid function access");
				}
					break;

				case ARG:
					if ( frames.size() > 0 )
					{
						frame &F = *frames.back();
						if ( F.iarg >= F.nargs )
							return error("too few arguments passed to function");

						size_t offset = F.thiscall ? 2 : 1;
						size_t idx = F.fp - F.nargs - offset + F.iarg;

						vardata_t *x = new vardata_t;
						x->assign( &stack[idx] );
						F.env.assign( identifiers[arg], x );
						F.iarg++;
					}
					break;

				case RET:
					if ( frames.size() > 1 )
					{
						
						vardata_t *result = &stack[sp-1];
						frame &F = *frames.back();
						size_t ncleanup = F.nargs + 1 + arg;
						if ( F.thiscall ) ncleanup++;

						if ( sp <= ncleanup ) 
							return error("stack corruption upon function return (sp=%d, nc=%d)", (int)sp, (int)ncleanup);
						sp -= ncleanup;
						stack[sp-1].copy( result->deref() );
						next_ip = F.retaddr;

						delete frames.back();
						frames.pop_back();
					}
					else
						next_ip = code_size;

					break;

				case END:
					next_ip = code_size;
					break;

				case NUL:
					CHECK_OVERFLOW();
					stack[sp].nullify();
					sp++;
					break;

				case DUP:
					CHECK_OVERFLOW();
					CHECK_FOR_ARGS( 1 );
					stack[sp].copy( stack[sp-1] );
					sp++;
					break;

				case VEC:
				{
					CHECK_FOR_ARGS( arg );
					if ( arg > 0 )
					{
						vardata_t &vv = stack[sp-arg];
						vardata_t save1;
						save1.copy( vv.deref() );
						vv.empty_vector();
						vv.vec()->resize( arg );
						vv.index(0)->copy( save1 );
						for( size_t i=1;i<arg;i++ )
							vv.index(i)->copy( stack[sp-arg+i].deref() );
						sp -= (arg-1);
					}
					else
					{
						CHECK_OVERFLOW();
						stack[sp].empty_vector();
						sp++;
					}
					break;
				}
				case HASH:
				{
					size_t N = arg*2;
					CHECK_FOR_ARGS( N );
					vardata_t &vv = stack[sp-N];
					lk_string key1( vv.deref().as_string() );
					vv.empty_hash();
					if ( arg > 0 )
					{
						for( size_t i=0;i<N;i+=2 )
							vv.hash_item( i==0 ? key1 :
								stack[sp-N+i].as_string() ).copy( 
								stack[sp-N+i+1].deref() );
					}
					sp -= (N-1);
					break;
				}
					
				default:
					return error( "invalid instruction (0x%02X)", (unsigned int)op );
				};

				ip = next_ip;

				nexecuted++;
				if ( mode == SINGLE && nexecuted > 0 ) return true;
			}
		} catch( std::exception &exc ) {
			return error("runtime exception @ %d: %s", (int)ip, exc.what() );
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
			pos = cpy.pos;
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
		lk::srcpos_t pos;
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
		std::vector<lk_string> &idList,
		std::vector<srcpos_t> &debugInfo )
	{
		if ( m_asm.size() == 0 ) return 0;

		bc.resize( m_asm.size(), 0 );
		debugInfo.resize( m_asm.size(), srcpos_t() );

		for( size_t i=0;i<m_asm.size();i++ )
		{
			instr &ip = m_asm[i];
			if ( ip.label ) m_asm[i].arg = m_labelAddr[ *ip.label ];
			bc[i] = (((unsigned int)ip.op)&0x000000FF) | (((unsigned int)ip.arg)<<8);
			debugInfo[i] = m_asm[i].pos;
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

			bool has_label = false;
			// determine if there's a label for this line (not super efficient)
			for( LabelMap::iterator it = m_labelAddr.begin();
				it != m_labelAddr.end();
				++it )
				if ( (int)i == it->second )
				{
					sprintf(buf, "%4s:", (const char*)it->first.c_str() );
					assembly += buf;
					has_label = true;
				}

			if ( !has_label )
				assembly += "     ";

			
			size_t j=0;
			while( op_table[j].name != 0 )
			{
				if ( ip.op == op_table[j].op )
				{
					sprintf( buf, "%4d  %4s ", ip.pos.line, op_table[j].name );
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
		return pfgen(root, F_NONE );
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
		if ( m_currentNode ) x.pos = m_currentNode->srcpos();
		m_asm.push_back( x );
		return m_asm.size();
	}

	int emit( Opcode o, const lk_string &L )
	{
		instr x(o, 0, (const char*) L.c_str());
		if ( m_currentNode ) x.pos = m_currentNode->srcpos();
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
						val.empty_vector();
						if ( !initialize_const_vec( dynamic_cast<list_t*>(expr->left), val ) )
							return false;
					}
					else if ( expr->oper == expr_t::INITHASH )
					{
						val.empty_hash();
						if ( !initialize_const_hash( dynamic_cast<list_t*>(expr->left), val ) )
							return false;
					}
					else
						return false;
				}
				else
					return false;

				vhash.hash_item(key).copy( val );
			}
			else
				return false;

			v = v->next;
		}

		return true;
	}

	bool pfgen_stmt( lk::node_t *root, unsigned int flags )
	{
		bool ok = pfgen( root, flags );
		// expressions always leave their value on the stack, so clean it up
		if (expr_t *e = dynamic_cast<expr_t*>(root)) emit( POP );
		return ok;
	}

	bool pfgen( lk::node_t *root, unsigned int flags )
	{
		m_currentNode = root;
		if ( !root ) return true;

		if ( list_t *n = dynamic_cast<list_t*>( root ) )
		{
			while( n )
			{
				if ( !pfgen_stmt( n->item, flags ) )
					return false;
				
				n=n->next;
			}
		}
		else if ( iter_t *n = dynamic_cast<iter_t*>( root ) )
		{
			if ( n->init && !pfgen_stmt( n->init, flags ) ) return false;

			// labels for beginning and end of loop
			lk_string Lb = new_label();
			lk_string Le = new_label();
			
			m_continueAddr.push_back( Lb );
			m_breakAddr.push_back( Le );

			place_label( Lb ) ;

			if ( !pfgen( n->test, flags ) ) return false;

			emit( JF, Le );
			
			pfgen_stmt( n->block, flags );

			if ( n->adv && !pfgen_stmt( n->adv, flags ) ) return false;

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
			pfgen_stmt( n->on_true, flags );
			if ( n->on_false )
			{
				L2 = new_label();
				emit( J, L2 );
				place_label( L1 );
				pfgen_stmt( n->on_false, flags );
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
				pfgen( n->left, flags );
				emit( DEC );
				break;
			case expr_t::LOGIOR:
			{
				lk_string Lsc = new_label();
				pfgen(n->left, flags );
				emit( DUP );
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
				emit( DUP );
				emit( JF, Lsc );
				pfgen(n->right, flags );
				emit( AND );
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
				// make space on stack for the return value
				emit( NUL );

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

				expr_t *lexpr = dynamic_cast<expr_t*>(n->left);
				if ( n->oper == expr_t::THISCALL && 0 != lexpr )
				{

					pfgen( lexpr->left, F_NONE );
					emit( DUP );
					pfgen( lexpr->right, F_NONE );
					emit( KEY );
				}
				else
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
				if ( iden_t *iden = dynamic_cast<iden_t*>( n->left ) )
					emit( TYP, place_identifier( iden->name ) );
				else
					return error( "invalid typeof expression, identifier required" );
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
					place_label( labels[idx++] );
					pfgen( p->item, F_NONE );
					emit( J, Le );
					p = p->next;
				}

				place_label( Le );
			}
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
					emit( RET, 0 );

				place_label( Le );
				emit( FREF, Lf );

			}
				break;

			default:
				return false;
			}
		}
		else if ( ctlstmt_t *n = dynamic_cast<ctlstmt_t*>( root ) )
		{
			switch( n->ictl )
			{
			case ctlstmt_t::RETURN:
				pfgen(n->rexpr, F_NONE );
				emit( RET, n->rexpr ? 1 : 0 );
				break;

			case ctlstmt_t::BREAK:
				if ( m_breakAddr.size() == 0 )
					return false;

				emit( J, m_breakAddr.back() );
				break;

			case ctlstmt_t::CONTINUE:
				if ( m_continueAddr.size() == 0 )
					return false;
				emit( J, m_continueAddr.back() );
				break;

			case ctlstmt_t::EXIT:
				emit( END );
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
				if ( n->constval && flags & F_MUTABLE ) op = CREF;
				else if ( flags & F_MUTABLE ) op = NREF;

				emit( op, place_identifier(n->name) );
			}
		}
		else if ( null_t *n = dynamic_cast<null_t*>(root) )
		{
			emit( NUL );
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

enum { ID_CODE = wxID_HIGHEST+149, ID_SAVE, ID_PARSE, ID_ASM, ID_BYTECODE, ID_OUTPUT, ID_DEBUG,
	ID_LOAD, ID_RESET, ID_STEP1, ID_VMRUN, ID_EVAL };

class VMTestFrame : public wxFrame
{
	lk::env_t *m_runEnv;
	static const int m_markCircle = 0;
	static const int m_markArrow = 1;
	static const int m_markLeftBox = 2;
	static const int m_lineNumMarginId = 0;
	static const int m_syntaxCheckMarginId = 1;
	static const int m_breakpointMarginId = 2;
	static const int m_foldingMarginId = 3;

	wxStyledTextCtrl *m_code;
	wxTextCtrl *m_parse, *m_bytecode, *m_output, *m_error, *m_debug;
	wxListBox *m_asm;
	lk::vm vm;

	std::vector<unsigned int> program;
	std::vector<lk::vardata_t> constants;
	std::vector<lk_string> identifiers;
	std::vector<lk::srcpos_t> debuginfo;
public:
	void ResetRunEnv()
	{
		if ( m_runEnv ) delete m_runEnv;
		m_runEnv = new lk::env_t;
		m_runEnv->register_func( output_cb, this );
		m_runEnv->register_func( rand_cb );
		m_runEnv->register_funcs( lk::stdlib_basic() );
		m_runEnv->register_funcs( lk::stdlib_math() );
		m_runEnv->register_funcs( lk::stdlib_string() );
		m_runEnv->register_funcs( lk::stdlib_wxui() );
	}

	VMTestFrame() : wxFrame( NULL, wxID_ANY, "LK-VM", wxDefaultPosition, wxSize(1200,900) )
	{
		m_runEnv = 0;
		
		wxFont font( 12, wxFONTFAMILY_MODERN, wxFONTSTYLE_NORMAL, wxFONTWEIGHT_NORMAL, false, "Consolas" );

		wxBoxSizer *buttons = new wxBoxSizer( wxHORIZONTAL );
		buttons->Add( new wxButton( this, ID_SAVE, "save code"), 0, wxALL|wxEXPAND, 3 );
		buttons->Add( new wxButton( this, ID_LOAD, "load bytecode"), 0, wxALL|wxEXPAND, 3 );
		buttons->Add( new wxButton( this, ID_RESET, "reset"), 0, wxALL|wxEXPAND, 3 );
		buttons->Add( new wxButton( this, ID_STEP1, "step"), 0, wxALL|wxEXPAND, 3 );
		buttons->Add( new wxButton( this, ID_VMRUN, "execvm"), 0, wxALL|wxEXPAND, 3 );
		buttons->Add( new wxButton( this, ID_EVAL, "interpret"), 0, wxALL|wxEXPAND, 3 );
		buttons->Add( m_error=new wxTextCtrl( this, wxID_ANY, "ready."), 1, wxALL|wxALIGN_CENTER_VERTICAL, 3 );
		m_error->SetForegroundColour( *wxRED );

		m_code = new wxStyledTextCtrl( this, ID_CODE );
		SetupCodeEditorStyle();

		m_parse = new wxTextCtrl( this, ID_PARSE, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_parse->SetFont( font );
		m_parse->SetForegroundColour( *wxBLUE );

		m_asm = new wxListBox( this, ID_ASM, wxDefaultPosition, wxDefaultSize, 0, 0, wxLB_HSCROLL );
		m_asm->SetFont( font );
		m_asm->SetForegroundColour( "Forest green" );
		
		m_bytecode = new wxTextCtrl( this, ID_BYTECODE, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_bytecode->SetFont( font );
		m_bytecode->SetForegroundColour( "Maroon" );
		
		m_output = new wxTextCtrl( this, ID_OUTPUT, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_output->SetForegroundColour( "Dark green" );
		
		m_debug = new wxTextCtrl( this, ID_DEBUG, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_debug->SetFont( font );
		m_debug->SetForegroundColour( "Maroon" );

		wxBoxSizer *hsizer = new wxBoxSizer( wxHORIZONTAL );
		hsizer->Add( m_code, 3, wxALL|wxEXPAND, 0 );
		hsizer->Add( m_parse, 1, wxALL|wxEXPAND, 0 );
		hsizer->Add( m_asm, 2, wxALL|wxEXPAND, 0 );
		hsizer->Add( m_bytecode, 1, wxALL|wxEXPAND, 0 );


		wxBoxSizer *tsizer = new wxBoxSizer( wxHORIZONTAL );
		tsizer->Add( m_debug, 2, wxALL|wxEXPAND, 0 );
		tsizer->Add( m_output, 1, wxALL|wxEXPAND, 0 );

		
		wxBoxSizer *vsizer = new wxBoxSizer( wxVERTICAL );
		vsizer->Add( buttons, 0, wxALL|wxEXPAND, 0 );		
		vsizer->Add( hsizer, 3, wxALL|wxEXPAND, 0 );
		vsizer->Add( tsizer, 1, wxALL|wxEXPAND, 0 );
		SetSizer(vsizer);

		m_code->LoadFile( wxGetHomeDir() + "/.lk-vm-code" );
		ParseAndGenerateAssembly();
	}
	virtual ~VMTestFrame() {
		if (m_runEnv) delete m_runEnv;
	}
	
	void SetupCodeEditorStyle()
	{
		static  char *LKWordlist1  =
	"if while for return exit break continue function const enum class else elseif define this typeof true false null import ";

		m_code->SetScrollWidthTracking( true );

		m_code->SetStyleBits( 8 );
		m_code->SetLayoutCache( wxSTC_CACHE_PAGE );
		m_code->SetLexer( wxSTC_LEX_NULL );
		
		wxFont font ( 12,
			wxFONTFAMILY_MODERN,
			wxFONTSTYLE_NORMAL,
			wxFONTWEIGHT_NORMAL,
			false,
			"Consolas" );

		m_code->SetFont( font );
		m_code->StyleSetFont (wxSTC_STYLE_DEFAULT, font);
		
		wxFont fontslant( font );
		fontslant.SetStyle( wxFONTSTYLE_ITALIC );
		
		wxFont fontsmall( font );
		fontsmall.SetPointSize( fontsmall.GetPointSize() - 1 );
	
		m_code->SetViewEOL( false );
		m_code->SetIndentationGuides( false );
		m_code->SetEdgeMode( wxSTC_EDGE_NONE );
		m_code->SetViewWhiteSpace( wxSTC_WS_INVISIBLE );
		m_code->SetOvertype( false );
		m_code->SetReadOnly( false );
		m_code->SetWrapMode( wxSTC_WRAP_NONE );
		m_code->StyleSetForeground( wxSTC_STYLE_DEFAULT, *wxBLACK );
		m_code->StyleSetBackground( wxSTC_STYLE_DEFAULT, *wxWHITE );
		m_code->StyleSetForeground( wxSTC_STYLE_INDENTGUIDE, *wxLIGHT_GREY );
		m_code->SetFoldFlags(0);

		// set spaces and indentation
		m_code->SetTabWidth( 4 );
		m_code->SetUseTabs( true );
		m_code->SetTabIndents( true );
		m_code->SetBackSpaceUnIndents( true );
		m_code->SetIndent( 4 );
		m_code->SetEdgeColumn( 80 );
		m_code->SetEdgeColour( wxColour(255,187,187) );
		m_code->SetEdgeMode( wxSTC_EDGE_LINE );
    
		// set visibility
		m_code->SetVisiblePolicy (wxSTC_VISIBLE_STRICT|wxSTC_VISIBLE_SLOP, 1);
		m_code->SetXCaretPolicy (wxSTC_CARET_EVEN|wxSTC_VISIBLE_STRICT|wxSTC_CARET_SLOP, 1);
		m_code->SetYCaretPolicy (wxSTC_CARET_EVEN|wxSTC_VISIBLE_STRICT|wxSTC_CARET_SLOP, 1);
	
		m_code->SetSelForeground( true, *wxWHITE );
		m_code->SetSelBackground( true, *wxBLACK );

		// markers
		m_code->MarkerDefine( wxSTC_MARKNUM_FOLDER,        wxSTC_MARK_DOTDOTDOT, *wxBLACK, *wxBLACK);
		m_code->MarkerDefine( wxSTC_MARKNUM_FOLDEROPEN,    wxSTC_MARK_ARROWDOWN, *wxBLACK, *wxBLACK);
		m_code->MarkerDefine( wxSTC_MARKNUM_FOLDERSUB,     wxSTC_MARK_EMPTY,     *wxBLACK, *wxBLACK);
		m_code->MarkerDefine( wxSTC_MARKNUM_FOLDEREND,     wxSTC_MARK_DOTDOTDOT, *wxBLACK, *wxWHITE);
		m_code->MarkerDefine( wxSTC_MARKNUM_FOLDEROPENMID, wxSTC_MARK_ARROWDOWN, *wxBLACK, *wxWHITE);
		m_code->MarkerDefine( wxSTC_MARKNUM_FOLDERMIDTAIL, wxSTC_MARK_EMPTY,     *wxBLACK, *wxBLACK);
		m_code->MarkerDefine( wxSTC_MARKNUM_FOLDERTAIL,    wxSTC_MARK_EMPTY,     *wxBLACK, *wxBLACK);
		
		m_code->CallTipUseStyle( 30 );
		wxFont fontnormal (*wxNORMAL_FONT) ;
		m_code->StyleSetFont( wxSTC_STYLE_CALLTIP, fontnormal );
		m_code->StyleSetForeground( wxSTC_STYLE_CALLTIP, *wxBLACK );
		m_code->StyleSetBackground( wxSTC_STYLE_CALLTIP, wxColour(247,240,210) );
		
		// set up line number margin
		m_code->SetMarginType( m_lineNumMarginId, wxSTC_MARGIN_NUMBER );
		m_code->StyleSetForeground( wxSTC_STYLE_LINENUMBER, wxColour(80,80,80) );
		m_code->StyleSetBackground( wxSTC_STYLE_LINENUMBER, wxColour(230,230,230) );
		int lineNrMarginWidth = m_code->TextWidth (wxSTC_STYLE_LINENUMBER, _T("_99999"));
		m_code->SetMarginWidth( m_lineNumMarginId, lineNrMarginWidth );

		// breakpoint margin	
		m_code->MarkerDefine( m_markCircle, wxSTC_MARK_CIRCLE );
		m_code->MarkerDefine( m_markArrow, wxSTC_MARK_SHORTARROW );
		m_code->SetMarginType( m_breakpointMarginId, wxSTC_MARGIN_SYMBOL );
		m_code->SetMarginWidth( m_breakpointMarginId, 0 );
		m_code->SetMarginSensitive( m_breakpointMarginId, false );

		m_code->SetLexer( wxSTC_LEX_CPP );
		 
		m_code->StyleSetForeground(wxSTC_C_COMMENT, wxColour(0x00, 0xaf, 0x00));
		m_code->StyleSetForeground(wxSTC_C_COMMENTLINE, wxColour(0x00, 0xaf, 0x00));
		m_code->StyleSetForeground(wxSTC_C_COMMENTDOC, wxColour(0xaf, 0xaf, 0xaf));
	
		m_code->StyleSetFont( wxSTC_STYLE_DEFAULT, font );
		m_code->StyleSetFont( wxSTC_C_DEFAULT, font );
		m_code->StyleSetFont( wxSTC_C_COMMENT, fontslant );
		m_code->StyleSetFont( wxSTC_C_COMMENTLINE, fontslant );
		m_code->StyleSetFont( wxSTC_C_COMMENTDOC, fontslant );

		m_code->StyleSetForeground(wxSTC_C_WORD, wxColour("red"));
		m_code->StyleSetForeground(wxSTC_C_WORD2,  wxColour(0,128,192));
		
		m_code->StyleSetForeground(wxSTC_C_NUMBER,  wxColour(0x00, 0x7f, 0x7f));

		wxColour cLiteral( "maroon" );
		m_code->StyleSetForeground(wxSTC_C_STRING, cLiteral );
		m_code->StyleSetForeground(wxSTC_C_STRINGEOL, cLiteral );
		m_code->StyleSetForeground(wxSTC_C_VERBATIM, cLiteral );
		m_code->StyleSetForeground(wxSTC_C_STRINGRAW, cLiteral );
		m_code->StyleSetForeground(wxSTC_C_TRIPLEVERBATIM, cLiteral );
		m_code->StyleSetForeground(wxSTC_C_HASHQUOTEDSTRING, cLiteral );
		
		m_code->StyleSetForeground(wxSTC_C_CHARACTER,  wxColour(0x7f, 0x00, 0x7f));
		m_code->StyleSetForeground(wxSTC_C_UUID,  wxColour(0x00, 0x7f, 0x7f));
		m_code->StyleSetForeground(wxSTC_C_PREPROCESSOR,  wxColour(0x7f, 0x7f, 0x7f));
		m_code->StyleSetForeground(wxSTC_C_OPERATOR, wxColour("blue"));
		m_code->StyleSetForeground(wxSTC_C_IDENTIFIER, wxColour(0x00, 0x00, 0x00));

		m_code->StyleSetBackground(wxSTC_STYLE_BRACELIGHT, *wxLIGHT_GREY );
		m_code->StyleSetForeground(wxSTC_STYLE_BRACELIGHT, *wxWHITE );
		

		m_code->SetKeyWords(wxSTC_C_DEFAULT, LKWordlist1 );
		m_code->SetMarginWidth(m_foldingMarginId, 0);
		m_code->SetProperty(wxT("fold"), "0");
	}

	static void rand_cb( lk::invoke_t &cxt )
	{
		LK_DOC("rand", "Generate a random number between 0 and 1.", "(none):number");
	static wxMTRand rng;
		cxt.result().assign( rng.rand() );
	}
	static void output_cb( lk::invoke_t &cxt )
	{
		LK_DOC("outln", "output data", "none" );
		VMTestFrame *frm = (VMTestFrame*)cxt.user_data();
		frm->m_output->AppendText( cxt.arg(0).as_string() + "\n");
	}

	void UpdateVMView()
	{
		size_t ip = vm.get_ip();
		if ( ip  < m_asm->GetCount() )
			m_asm->SetSelection( ip );

		if ( ip < debuginfo.size() )
		{
			int line = debuginfo[ip].line;
			if ( line > 0 && line <= m_code->GetNumberOfLines() )
			{
				m_code->ScrollToLine( line-1 );
				m_code->MarkerDeleteAll(m_markArrow );
				m_code->MarkerAdd( line-1, m_markArrow );
			}
		}
		
		size_t sp = 0;
		lk::vardata_t *stack = vm.get_stack( &sp );
		wxString sout = wxString::Format("[%d]:\n", (int)sp);
		for( size_t i=0;i<sp;i++ )
		{
			lk::vardata_t &sval = stack[sp-i-1];
			sout += "\t" + sval.as_string() + "\t\t(" + sval.typestr() + ")\n";
		}
		sout += "----------------\n\n";

		size_t nfrm = 0;
		lk::vm::frame **frames = vm.get_frames( &nfrm );
		for( size_t i=0;i<nfrm;i++ )
		{
			lk::vm::frame &F = *frames[nfrm-i-1];
			sout += wxString::Format( "frame[%d] ret=%d fp=%d iarg=%d narg=%d %s\n", 
				nfrm-i-1, F.retaddr, F.fp, F.iarg, F.nargs, F.thiscall ? "(thiscall)" : "" );
			lk_string key;
			lk::vardata_t *val;
			bool has_more = F.env.first( key, val );
			while( has_more )
			{
				sout += "\t" + key + "=" + val->as_string() + "\t\t(" + val->typestr() + ")\n";
				has_more = F.env.next( key, val );
			}
		}

		std::vector< size_t > opcnt( (size_t)lk::__MaxOp, 0 );
		vm.get_opcount( &opcnt[0] );
		
		sout += "\nopcode frequency:\n";
		for( size_t i=0;i<(size_t)lk::__MaxOp;i++ )
			sout += wxString::Format("%s\t%d\n", lk::op_table[i].name, (int)opcnt[i]);
		sout+="\n";

		m_debug->ChangeValue( sout );
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
				if ( cg.build( node ) ) {
					cg.output( assembly, bytecode );
					cg.bytecode( program, constants, identifiers, debuginfo );
				}
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
		m_asm->Freeze();
		m_asm->Clear();
		m_asm->Append( wxStringTokenize(assembly, "\n") );
		m_asm->Thaw();
		m_bytecode->ChangeValue( bytecode );

	}

	void OnClose( wxCloseEvent &evt )
	{
		SaveCode();
		wxTheApp->ScheduleForDestruction( this );
	}

	void SaveCode()
	{
		wxString file(wxGetHomeDir() + "/.lk-vm-code");
		wxBusyInfo inf("writing " + file );
		if (! m_code->SaveFile( file ) )
			wxMessageBox("error saving code to file:\n\n" + file );
		wxYield();
		wxMilliSleep(150);
	}

	void OnCommand( wxCommandEvent &evt )
	{
		switch( evt.GetId() )
		{
		case ID_SAVE:			
			SaveCode();
			break;
		case ID_CODE:
			ParseAndGenerateAssembly();
			break;
		case ID_LOAD:
			ResetRunEnv();
			vm.load( program, constants, identifiers, debuginfo );
			m_debug->ChangeValue(
				wxString::Format("vm loaded %d instructions, %d constants, %d identifiers.\n",
					(int) program.size(), (int)constants.size(), (int)identifiers.size() ) );
			m_output->Clear();
			vm.restart();
			UpdateVMView();
			break;
		case ID_RESET:
			ResetRunEnv();
			vm.restart();
			UpdateVMView();
			break;
		case ID_STEP1:
			vm.run( lk::vm::SINGLE, m_runEnv );
			m_error->ChangeValue( vm.error() );			
			UpdateVMView();
			break;
		case ID_VMRUN:
		{
			wxStopWatch sw;
			ResetRunEnv();
			vm.run( lk::vm::NORMAL, m_runEnv );
			long ms = sw.Time();
			m_error->ChangeValue( vm.error() );			
			UpdateVMView();
			m_output->AppendText( wxString::Format("\ncompleted in %d ms\n", ms ) );
			break;
		}

		case ID_EVAL:
			{
				lk::input_string input( m_code->GetValue() );
				lk::parser parse( input );
				if ( lk::node_t *node = parse.script() )
				{
					if ( parse.error_count() == 0 )
					{
						ResetRunEnv();
						lk::env_t myenv( m_runEnv );
						lk::eval ev( node, &myenv );
						wxStopWatch sw;
						bool ok = ev.run();
						long ms = sw.Time();
						if ( !ok )
						{
							for( size_t i=0;i<ev.error_count();i++ )
								m_output->AppendText( ev.get_error(i) + "\n");
						}
						m_output->AppendText( wxString::Format("\ncompleted in %d ms\n", ms ) );
					}
					else
						m_output->AppendText(" parse errors? ");

					delete node;
				}
			}
			break;
		}
	}

	void OnCodeModify( wxStyledTextEvent &evt )
	{
		if ( evt.GetModificationType() & wxSTC_MOD_INSERTTEXT 
			|| evt.GetModificationType() & wxSTC_MOD_DELETETEXT )
			ParseAndGenerateAssembly();
	}

	DECLARE_EVENT_TABLE()
};

BEGIN_EVENT_TABLE( VMTestFrame, wxFrame )
	EVT_CLOSE( VMTestFrame::OnClose )
	EVT_STC_MODIFIED( ID_CODE, VMTestFrame::OnCodeModify )
	EVT_BUTTON( wxID_ANY, VMTestFrame::OnCommand )
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
