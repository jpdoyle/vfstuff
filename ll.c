#include <stdlib.h>

typedef struct List {
   int x;
   struct List* next;
} List;

// slight cludge to work around List** deficiency in VF's parser
typedef List* List_ptr;

/*@
// "vals" is an inductive list of ints extracted from the heap
predicate linked_list(List* head; list<int> vals) =
    head == 0 ? vals == nil
              :     head->x    |-> ?val
                &*& head->next |-> ?nextHead
                &*& linked_list(nextHead,?rest)
                &*& vals == cons(val,rest)
                &*& malloc_block_List(head)
              ;

lemma_auto void linked_list_auto()
    requires [?f]linked_list(?head,?vals);
    ensures  [ f]linked_list( head, vals)
        &*&  (head == 0) == (vals == nil)
        ;
{ open linked_list(_,_); }

lemma_auto(append(reverse(a),cons(x,b)))
void append_reverse_cons<t>(list<t> a, t x, list<t> b)
    requires true;
    ensures  append(reverse(a),cons(x,b))
        ==   append(reverse(cons(x,a)),b);
{ append_assoc(reverse(a),{x},b); }

  @*/

void list_push(List** head,int v)
    /*@ requires *head |-> ?head_ptr &*& linked_list(head_ptr,?vals);
      @*/
    /*@ ensures  *head |-> ?new_head_ptr
            &*&  linked_list(new_head_ptr, cons(v,vals));
      @*/
    /*@ terminates; @*/
{
    List* node = malloc(sizeof(List));

    if(!node) abort();

    node->x = v;

    node->next = *head;
    *head = node;
}

bool list_pop(List** head,int* dst)
    /*@ requires *head |-> ?head_ptr &*& linked_list(head_ptr,?vals)
            &*&  *dst  |-> ?orig_dst;
      @*/
    /*@ ensures  *head |-> ?new_head_ptr
            &*&  linked_list(new_head_ptr, ?new_vals)
            &*&  *dst |-> ?new_dst
            &*&  head_ptr == 0
            ?    new_head_ptr == 0 &*& new_dst == orig_dst &*& !result
            :    vals == cons(new_dst,new_vals) &*& !!result
            ;
      @*/
    /*@ terminates; @*/
{
    List* h = *head;
    if(h) {
        *dst = h->x;
        *head = h->next;
        free(h);
        return true;
    }
    return false;
}

int list_length(List* head)
    /*@ requires [?f]linked_list(head,?vals)
            &*&  length(vals) <= INT_MAX; 
      @*/
    /*@ ensures  [ f]linked_list(head, vals)
            &*&  result == length(vals);
      @*/
    /*@ terminates; @*/
{
    int ret = 0;

    while(head)
        /*@ requires [f]linked_list(    head,?loop_vals)
                &*&  ret + length(loop_vals) <= INT_MAX;
          @*/
        /*@ ensures  [f]linked_list(old_head, loop_vals)
                &*&  ret == old_ret + length(loop_vals);
          @*/
        /*@ decreases length(loop_vals); @*/
    {
        head = head->next;
        ++ret;
    }

    return ret;
}

void list_append(List** a, List* b)
    /*@ requires *a |-> ?a_ptr
            &*&  linked_list(a_ptr,?a_vals)
            &*&  linked_list(b,?b_vals);
      @*/
    /*@ ensures  *a |-> ?new_a
            &*&  linked_list(new_a,append(a_vals,b_vals));
      @*/
    /*@ terminates; @*/
{
    List_ptr* p;
    p = a;
    while(true)
        /*@ requires *p |-> ?loop_p
                &*&  linked_list(loop_p,?p_vals)
                &*&  linked_list(b, b_vals);
          @*/
        /*@ ensures  *old_p |-> ?new_p
                &*&  loop_p == 0
                ?    linked_list(new_p, b_vals)
                :    new_p == loop_p
                &*&  linked_list(loop_p,
                                 append(p_vals,b_vals)); @*/
        /*@ decreases length(p_vals); @*/
    {
        if(*p) {
            p = &(*p)->next;
        } else {
            *p = b;
            break;
        }
    }
}

void list_reverse(List** head)
    /*@ requires *head |-> ?head_ptr &*& linked_list(head_ptr,?vals);
      @*/
    /*@ ensures  *head |-> ?new_ptr
            &*&  linked_list(new_ptr, reverse(vals));
      @*/
    /*@ terminates; @*/
{
    List* ret = 0;
    List* h = *head;

    while(h)
        /*@ requires linked_list(ret,?ret_vals)
                &*&  linked_list(h,?head_vals)
                &*&  vals == append(reverse(ret_vals),head_vals);
          @*/
        /*@ ensures  linked_list(ret,reverse(vals))
                &*&  linked_list(h,{})
                ;
          @*/
        /*@ decreases length(head_vals); @*/
    {
        List* node = h;
        h = h->next;
        node->next = ret;
        ret = node;
    }

    *head = ret;
}

