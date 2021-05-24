
section json

section has_to_json                                                                                 
universe u                                                                                          
                                                                                                    
meta class has_to_json (α : Type u) : Type (u+1) :=                                                 
(to_json : α → json)                                                                                
                                                                                                    
meta class has_to_tactic_json (α : Type u) : Type (u+1) :=                                          
(to_tactic_json : α → tactic json)                                                                  
                                                                                                    
meta class has_from_json (α : Type u) : Type (u+1) :=                                               
(from_json : json → tactic α)                                                                       
                                                                                                    
end has_to_json               

end json


