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

enum { ID_CODE = wxID_HIGHEST+149, ID_PARSE, ID_ASM };

lk_string lk_code_gen( lk::node_t *node )
{
	return "";
}

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
				assembly = lk_code_gen( node );
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
