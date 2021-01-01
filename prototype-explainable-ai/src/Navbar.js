import React from 'react';

function NavBar() {
    return (
        <header>
            <nav className="navbar navbar-light bg-light">
                <div className="container-fluid justify-content-center">
                    <div className="row">
                        <div className="col-md text-center">
                            <h2>Explainable AI</h2>
                        </div>
                        <div className="col-md text-center">
                            <a href="#" className="link-primary">Primary link</a>
                        </div>
                    </div>
                </div>
            </nav>
        </header>
    )
}

export default NavBar;