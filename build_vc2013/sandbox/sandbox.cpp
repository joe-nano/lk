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

#include <lk_absyn.h>
#include <lk_env.h>
#include <lk_stdlib.h>
#include <lk_eval.h>
#include <lk_lex.h>
#include <lk_invoke.h>
#include <lk_parse.h>


namespace lk {

enum Opcode {
	ADD, SUB, MUL, DIV, LT, GT, LE, GE, NE, EQ, INC, DEC, OR, AND, NOT, NEG, EXP, PSH, POP, ARG,
	J, JF, JT, IDX, KEY, MAT, WAT, SET, GET, WR, REF, FREF, CALL, TCALL, RET, SZ, KEYS, TYP, VEC, HASH,
	__InvalidOp };

struct { Opcode op; const char *name; } op_table[] = {
	{ ADD, "add" },
	{ SUB, "sub" },
	{ MUL, "mul" },
	{ DIV, "div" },
	{ LT, "lt" },
	{ GT, "gt" },
	{ LE, "le" },
	{ GE, "ge" },
	{ NE, "ne" },
	{ EQ, "eq" },
	{ INC, "inc" },
	{ DEC, "dec" },
	{ OR, "or" },
	{ AND, "and" },
	{ NOT, "not" },
	{ NEG, "neg" },
	{ EXP, "exp" },
	{ PSH, "psh" },
	{ POP, "pop" },
	{ ARG, "arg" },
	{ J, "j" },
	{ JF, "jf" },
	{ JT, "jt" },
	{ IDX, "idx" },
	{ KEY, "key" },
	{ MAT, "mat" },
	{ WAT, "wat" },
	{ SET, "set" },
	{ GET, "get" },
	{ WR, "wr" },
	{ REF, "ref" },
	{ FREF, "fref" },
	{ CALL, "call" },
	{ TCALL, "tcall" },
	{ RET, "ret" },
	{ SZ, "sz" },
	{ KEYS, "keys" },
	{ TYP, "typ" },
	{ VEC, "vec" },
	{ HASH, "hash" },
	{ __InvalidOp, 0 } };

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
	};

	std::vector<instr> m_asm;
	unordered_map< lk_string, int, lk_string_hash, lk_string_equal > m_labelAddr;
	std::vector< vardata_t > m_constData;
	std::vector< lk_string > m_idList;
	int m_labelCounter;
	std::vector<lk_string> m_breakAddr, m_continueAddr;

public:
	code_gen() {
		m_labelCounter = 1;
	}
	
	lk_string assemble()
	{
		char buf[1024];
		lk_string output;
		
		for( size_t i=0;i<m_asm.size();i++ )
		{
			instr &ip = m_asm[i];

			if ( ip.label )
				ip.arg = m_labelAddr[ *ip.label ];

			size_t j=0;
			while( op_table[j].name != 0 )
			{
				if ( ip.op == op_table[j].op )
				{
					sprintf(buf, "%6d: %4s (%02X)   %07d\n",
						(int)i, op_table[j].name, (int)ip.op, ip.arg );
					output += buf;
					break;
				}
				j++;
			}
		}
		
		for( size_t i=0;i<m_constData.size();i++ )
			output += ".data " + m_constData[i].as_string() + "\n";

		for( size_t i=0;i<m_idList.size();i++ )
			output += ".id " + m_idList[i] + "\n";

		return output;
	}

	bool build( lk::node_t *root )
	{
		m_idList.clear();
		m_constData.clear();
		m_asm.clear();
		m_labelAddr.clear();
		m_labelCounter = 0;
		m_breakAddr.clear();
		m_continueAddr.clear();
		bool ok = pfgen(root);
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
		m_asm.push_back( x );
		return m_asm.size();
	}

	int emit( Opcode o, const lk_string &L )
	{
		m_asm.push_back( instr(o, 0, (const char*) L.c_str()) );
		return m_asm.size();
	}

	bool pfgen( lk::node_t *root )
	{
		if ( !root ) return true;

		if ( list_t *n = dynamic_cast<list_t*>( root ) )
		{
			while( n )
			{
				if ( !pfgen( n->item ) )
					return false;

				n=n->next;
			}
		}
		else if ( iter_t *n = dynamic_cast<iter_t*>( root ) )
		{
			if ( n->init && !pfgen( n->init ) ) return false;

			// labels for beginning and end of loop
			lk_string Lb = new_label();
			lk_string Le = new_label();
			
			m_continueAddr.push_back( Lb );
			m_breakAddr.push_back( Le );

			place_label( Lb ) ;

			if ( !pfgen( n->test ) ) return false;

			emit( JF, Le );
			
			pfgen( n->block );

			if ( n->adv && !pfgen( n->adv ) ) return false;

			emit( J, Lb );
			place_label( Le );

			m_continueAddr.pop_back();
			m_breakAddr.pop_back();
		}
		else if ( cond_t *n = dynamic_cast<cond_t*>( root ) )
		{	
			lk_string L1 = new_label();
			lk_string L2 = L1;

			pfgen( n->test );
			emit( JF, L1 );
			pfgen( n->on_true );
			if ( n->on_false )
			{
				L2 = new_label();
				emit( J, L2 );
				place_label( L1 );
				pfgen( n->on_false );
			}
			place_label( L2 );
		}
		else if ( expr_t *n = dynamic_cast<expr_t*>( root ) )
		{
			switch( n->oper )
			{
			case expr_t::PLUS:
				pfgen( n->left );
				pfgen( n->right );
				emit( ADD );
				break;
			case expr_t::MINUS:
				pfgen( n->left );
				pfgen( n->right );
				emit( SUB );
				break;
			case expr_t::MULT:
				pfgen( n->left );
				pfgen( n->right );
				emit( MUL );
				break;
			case expr_t::DIV:
				pfgen( n->left );
				pfgen( n->right );
				emit( DIV );
				break;
			case expr_t::LT:
				pfgen( n->left );
				pfgen( n->right );
				emit( LT );
				break;
			case expr_t::GT:
				pfgen( n->left );
				pfgen( n->right );
				emit( GT );
				break;
			case expr_t::LE:
				pfgen( n->left );
				pfgen( n->right );
				emit( LE );
				break;
			case expr_t::GE:
				pfgen( n->left );
				pfgen( n->right );
				emit( GE );
				break;
			case expr_t::NE:
				pfgen( n->left );
				pfgen( n->right );
				emit( NE );
				break;
			case expr_t::EQ:
				pfgen( n->left );
				pfgen( n->right );
				emit( EQ );
				break;
			case expr_t::INCR:
				pfgen( n->left );
				emit( INC );
				break;
			case expr_t::DECR:
				pfgen( n->right );
				emit( DEC );
				break;
			case expr_t::LOGIOR:
			{
				lk_string Lsc = new_label();
				pfgen(n->left );
				emit( PSH, const_value(0) );
				emit( NE );
				emit( JT, Lsc );
				pfgen(n->right);
				emit( OR );
				place_label( Lsc );
			}
				break;
			case expr_t::LOGIAND:
			{
				lk_string Lsc = new_label();
				pfgen(n->left );
				emit( PSH, const_value(0) );
				emit( EQ );
				emit( JT, Lsc );
				pfgen(n->right );
				emit( OR );
				place_label( Lsc );
			}
				break;
			case expr_t::NOT:
				pfgen(n->left);
				emit( NOT );
				break;
			case expr_t::NEG:
				pfgen(n->left);
				emit( NEG );
				break;				
			case expr_t::EXP:
				pfgen(n->left);
				pfgen(n->right);
				emit( EXP );
				break;
			case expr_t::INDEX:
				pfgen(n->left);
				pfgen(n->right);
				emit( IDX );
				break;
			case expr_t::HASH:
				pfgen(n->left);
				pfgen(n->right);
				emit( KEY );
				break;
			case expr_t::MINUSAT:
				pfgen(n->left );
				pfgen(n->right);
				emit( MAT );
				break;
			case expr_t::WHEREAT:
				pfgen(n->left);
				pfgen(n->right);
				emit( WAT );
				break;
			case expr_t::PLUSEQ:
				pfgen(n->left);
				pfgen(n->right);
				emit( ADD );
				pfgen(n->left);
				emit( WR );
				break;
			case expr_t::MINUSEQ:
				pfgen(n->left);
				pfgen(n->right);
				emit( SUB );
				pfgen(n->left);
				emit( WR );
				break;
			case expr_t::DIVEQ:
				pfgen(n->left);
				pfgen(n->right);
				emit( DIV );
				pfgen(n->left);
				emit( WR );
				break;
			case expr_t::ASSIGN:
				{
					if ( !pfgen( n->right ) ) return false;

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

					if ( !pfgen( n->left ) ) return false;
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
					pfgen( p->item );
					p = p->next;
					nargs++;
				}

				pfgen( n->left );
				emit( (n->oper == expr_t::THISCALL)? TCALL : CALL, nargs );
			}
				break;
			case expr_t::SIZEOF:
				pfgen( n->left );
				emit( SZ );
				break;
			case expr_t::KEYSOF:
				pfgen( n->left );
				emit( KEYS );
				break;
			case expr_t::TYPEOF:
				pfgen( n->left );
				emit( TYP );
				break;
			case expr_t::INITVEC:
			{
				int len = 0;
				list_t *p = dynamic_cast<list_t*>( n->left );
				while( p )
				{
					pfgen( p->item );
					p = p->next;
					len++;
				}
				emit( VEC, len );
			}
				break;
			case expr_t::INITHASH:
			{
				int npairs = 0;
				list_t *p = dynamic_cast<list_t*>( n->left );
				while (p)
				{
					expr_t *assign = dynamic_cast<expr_t*>(p->item);
					if (assign && assign->oper == expr_t::ASSIGN)
					{
						pfgen( assign->left );
						pfgen( assign->right );
					}
					p = p->next;
					npairs++;
				}
				emit( HASH, npairs );
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
					pfgen( n->left );
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
					pfgen( p->item );
					emit( J, Le );
					p = p->next;
				}

				place_label( Le );
			}
				break;

			case expr_t::RETURN:
				pfgen(n->left);
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

				pfgen( n->right );

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
				emit( REF, place_identifier(n->name) );
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

enum { ID_CODE = wxID_HIGHEST+149, ID_PARSE, ID_ASM, ID_OUTPUT };

class VMTestFrame : public wxFrame
{
	wxTextCtrl *m_code, *m_parse, *m_asm, *m_output;
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
		m_asm->SetForegroundColour( "Dark green" );
		
		m_output = new wxTextCtrl( this, ID_OUTPUT, wxEmptyString, wxDefaultPosition, wxDefaultSize, wxTE_MULTILINE );
		m_output->SetFont( font );
		m_output->SetForegroundColour( "Dark green" );

		wxBoxSizer *hsizer = new wxBoxSizer( wxHORIZONTAL );
		hsizer->Add( m_code, 1, wxALL|wxEXPAND, 0 );
		hsizer->Add( m_parse, 1, wxALL|wxEXPAND, 0 );
		hsizer->Add( m_asm, 1, wxALL|wxEXPAND, 0 );

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
		wxString output, assembly;
		lk::input_string input( m_code->GetValue() );
		lk::parser parse( input );
		if ( lk::node_t *node = parse.script() )
		{
			if ( parse.error_count() == 0 )
			{
				lk::pretty_print( output, node, 0 );
				lk::code_gen cg;
				if ( cg.build( node ) ) assembly = cg.assemble();
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
