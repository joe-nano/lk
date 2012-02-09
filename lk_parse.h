#ifndef __lk_parse_h
#define __lk_parse_h

#include <vector>
#include "lk_lex.h"
#include "lk_absyn.h"

namespace lk
{
	class LKEXPORT importer
	{
	public:
		virtual bool read_source( const lk_string &path, 
			lk_string *expandedPath, lk_string *data ) = 0;
	};

	class LKEXPORT parser
	{
	public:
		parser( input_base &input, const lk_string &name = "" );

		void set_importer( importer *imploc );
		void set_importer( importer *imploc, const std::vector< lk_string > &imported_names );
				
		node_t *script();
		node_t *block();
		node_t *statement();
		node_t *test();
		node_t *enumerate();
		node_t *loop();
		node_t *define();
		node_t *assignment();		
		node_t *ternary();
		node_t *logicalor();
		node_t *logicaland();
		node_t *equality();
		node_t *relational();
		node_t *additive();
		node_t *multiplicative();
		node_t *exponential();
		node_t *unary();
		node_t *postfix();
		node_t *primary();		
		
		int line() { return lex.line(); }
		int error_count() { return m_errorList.size(); }
		lk_string error(int idx);
		
		int token();
		bool token(int t);
		
		void skip();
		bool match(int t);
		bool match( const char *s );
		
	private:
		list_t *ternarylist( int septok, int endtok );
		list_t *identifierlist( int septok, int endtok );
	
		void error( const char *fmt, ... );
		
		lexer lex;				
		int m_tokType;		
		lk_string m_lexError;
		bool m_haltFlag;
		std::vector<lk_string> m_errorList;
		importer *m_importer;
		std::vector< lk_string > m_importNameList;
		lk_string m_name;
	};
};

#endif
