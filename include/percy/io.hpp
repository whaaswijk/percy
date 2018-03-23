#pragma once

namespace percy
{

    /***************************************************************************
        Converts a DAG to the folling string format:
        "n,r,j_1,k_1,j_2,k_2,...,j_r,k_r", where
        n is the number of input variables
        r is the number of internal nodes (or steps)
        the r pairs (j_i, k_i) represent the internal nodes and their incoming
        arcs.
        The resulting string is written to the supplied character buffer and
        will be null terminated.
        NOTE: the function assumes that enough memory has been allocated in
        the buffer.
    ***************************************************************************/
    template<class Dag=dag<2>>
    void dag_to_string(const Dag& g, char* buf)
    {
        buf[0] = char(g.nr_vars() + '0');
        buf[1] = ',';
        buf[2] = char(g.nr_vertices() + '0');
        buf[3] = ',';
        int i = 0;
        for (i = 0; i < g.nr_vertices(); i++) {
            const auto& vertex = g.get_vertex(i);
            buf[i*4+4] = char(vertex.first + '0');
            buf[i*4+5] = ',';
            buf[i*4+6] = char(vertex.second + '0');
            if (i != g.nr_vertices() - 1) {
                buf[i*4+7] = ',';
            }
        }
        buf[i*4+3] = '\0';
    }


    /***************************************************************************
        Parses a DAG string into a DAG object.
    ***************************************************************************/
    template<class Dag=dag<2>>
    void dag_read_string(Dag& g, char* buf)
    {
    }

    /***************************************************************************
        Converts a dag to the graphviz dot format and writes it to the
        specified output stream.
    ***************************************************************************/
    template<class Dag>
    void to_dot(Dag& dag, std::ostream& o)
    {
        o << "graph{\n";
        o << "rankdir = BT\n";
        dag.foreach_input([&o] (int input_idx) {
            const auto dot_idx = input_idx +1;
            o << "x" << dot_idx << " [shape=none,label=<x<sub>" << dot_idx 
                << "</sub>>];\n";
        });

        o << "node [shape=circle];\n";
        dag.foreach_vertex([&dag, &o] (int v_idx) {
            const auto v = dag.get_vertex(v_idx);
            const auto dot_idx = dag.get_nr_inputs() + v_idx + 1;
            o << "x" << dot_idx << " [label=<x<sub>" << dot_idx 
                << "</sub>>];\n";

            dag.foreach_fanin(v, [&o, dot_idx] (typename Dag::fanin f_id) {
                o << "x" << f_id+1 << " -- x" << dot_idx << ";\n";
            });

        });

        // Group inputs on same level.
        o << "{rank = same; ";
        for (int i = 0; i < dag.get_nr_inputs(); i++) {
            o << "x" << i+1 << "; ";
        }
        o << "}\n";

        // Add invisible edges between PIs to enforce order.
        o << "edge[style=invisible];\n";
        for (int i = dag.get_nr_inputs(); i > 1; i--) {
            o << "x" << i-1 << " -- x" << i << ";\n";
        }

        o << "}\n";
    }
}

