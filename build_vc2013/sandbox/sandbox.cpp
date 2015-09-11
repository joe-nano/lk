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

class code_gen
{
private:
	int m_labelCounter;
	lk_string m_output;
	lk_string m_error;

public:
	code_gen() {
		m_labelCounter = 0;
	}

	lk_string assembly() { return m_output; }
	lk_string error() { return m_error; }

	lk_string label()
	{
		return lk::format( "L%d", m_labelCounter++ );
	}

	void emit( const lk_string &s )
	{
		if ( s.IsEmpty() ){
			m_output += "\n";
			return;
		}

		if ( s[0] == 'L' )
			m_output += s + "\n";
		else
			m_output += "   " + s + "\n";
	}

	enum Ctl { FAIL, OK, BREAK, CONTINUE, RETURN, EXIT };

	Ctl eval( lk::node_t *root )
	{
		if ( !root ) return OK;

		if ( list_t *n = dynamic_cast<list_t*>( root ) )
		{
			while( n )
			{
				if ( !eval( n->item ) )
					return FAIL;

				n=n->next;
			}
		}
		else if ( iter_t *n = dynamic_cast<iter_t*>( root ) )
		{
			if ( n->init && !eval( n->init ) ) return FAIL;

			// labels for beginning and end of loop
			lk_string Lb = label();
			lk_string Le = label();

			emit( Lb ) ;

			if ( !eval( n->test ) ) return FAIL;

			emit( "jf " + Le );

			Ctl c = eval( n->block );
			switch( c )
			{
			case FAIL: return FAIL;
			case BREAK: emit( "j " + Lb ); break;
			case EXIT: emit( "end" ); break;
			case RETURN: emit("ret"); break;
			case CONTINUE:
			case OK:
				break;
			}


			if ( n->adv && !eval( n->adv ) ) return FAIL;

			emit ("j " + Lb );
			emit( Le );
		}
		else if ( cond_t *n = dynamic_cast<cond_t*>( root ) )
		{	
			lk_string L1 = label();
			lk_string L2 = L1;

			eval( n->test );
			emit( "jf " + L1 );
			eval( n->on_true );
			if ( n->on_false )
			{
				L2 = label();
				emit( "j " + L2 );
				emit( L1 );
				eval( n->on_false );
			}
			emit( L2 );
		}
		else if ( expr_t *n = dynamic_cast<expr_t*>( root ) )
		{
			switch( n->oper )
			{
			case expr_t::PLUS:
				eval( n->left );
				eval( n->right );
				emit( "add" );
				break;
			case expr_t::MINUS:
				eval( n->left );
				eval( n->right );
				emit( "sub" );
				emit( "neg" );
				break;
			case expr_t::MULT:
				eval( n->left );
				eval( n->right );
				emit( "mul" );
				break;
			case expr_t::DIV:
				eval( n->left );
				eval( n->right );
				emit( "div" );
				break;
			case expr_t::LT:
				eval( n->left );
				eval( n->right );
				emit( "lt" );
				break;
			case expr_t::GT:
				eval( n->left );
				eval( n->right );
				emit( "gt" );
				break;
			case expr_t::LE:
				eval( n->left );
				eval( n->right );
				emit( "le" );
				break;
			case expr_t::GE:
				eval( n->left );
				eval( n->right );
				emit( "ge" );
				break;
			case expr_t::NE:
				eval( n->left );
				eval( n->right );
				emit( "ne" );
				break;
			case expr_t::EQ:
				eval( n->left );
				eval( n->right );
				emit( "eq" );
				break;
			case expr_t::ASSIGN:
				{
					if ( !eval( n->right ) ) return FAIL;

					bool sset = false;
					// if on the LHS of the assignment we have a special variable i.e. ${xy}, use a 
					// hack to assign the value to the storage location
					if ( lk::iden_t *iden = dynamic_cast<lk::iden_t*>(n->left) )
					{
						if ( iden->special )
						{
							emit( "store! " + iden->name );
							return OK;
						}
					}

					if ( !eval( n->left ) ) return FAIL;
					emit( "store" );
				}
				break;
			default:
				m_error = lk_string("unsupported expression: ") + n->operstr();
				return FAIL;
			}
		}
		else if ( iden_t *n = dynamic_cast<iden_t*>( root ) )
		{			
			if ( n->special )
			{
				emit( "load! " + n->name );
				return OK;;
			}
			else
				emit( "load " + n->name );
		}
		else if ( constant_t *n = dynamic_cast<constant_t*>(root ) )
		{
			emit( "push " + lk::format("%lg",n->value) );
		}
		else if ( literal_t *n = dynamic_cast<literal_t*>(root ) )
		{
			emit( "push '" + n->value + "'" );
		}

		return OK;
	}
};

}; // namespace lk

enum { ID_CODE = wxID_HIGHEST+149, ID_PARSE, ID_ASM };

class VMTestFrame : public wxFrame
{
	wxTextCtrl *m_code, *m_parse, *m_asm;
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

		wxBoxSizer *sizer = new wxBoxSizer( wxHORIZONTAL );
		sizer->Add( m_code, 1, wxALL|wxEXPAND, 0 );
		sizer->Add( m_parse, 1, wxALL|wxEXPAND, 0 );
		sizer->Add( m_asm, 1, wxALL|wxEXPAND, 0 );
		SetSizer(sizer);

		m_code->LoadFile( wxGetHomeDir() + "/.lk-vm-code" );
		ParseAndGenerateAssembly();
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
				if ( cg.eval( node ) ) assembly = cg.assembly();
				else assembly = cg.error();
			}
			else
			{
				for( int i=0;i<parse.error_count();i++ )
					output += parse.error(i) + "\n";
			}

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
