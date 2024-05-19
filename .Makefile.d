theories.vo theories.glob theories.v.beautified theories.required_vo: theories.v 
theories.vio: theories.v 
theories.vos theories.vok theories.required_vos: theories.v 
facts.vo facts.glob facts.v.beautified facts.required_vo: facts.v theories.vo
facts.vio: facts.v theories.vio
facts.vos facts.vok facts.required_vos: facts.v theories.vos
relational_ka.vo relational_ka.glob relational_ka.v.beautified relational_ka.required_vo: relational_ka.v theories.vo facts.vo
relational_ka.vio: relational_ka.v theories.vio facts.vio
relational_ka.vos relational_ka.vok relational_ka.required_vos: relational_ka.v theories.vos facts.vos
language_ka.vo language_ka.glob language_ka.v.beautified language_ka.required_vo: language_ka.v theories.vo facts.vo
language_ka.vio: language_ka.v theories.vio facts.vio
language_ka.vos language_ka.vok language_ka.required_vos: language_ka.v theories.vos facts.vos
